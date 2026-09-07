import KR21Monoculture.Family
import KR21Monoculture.FiberSigns
import KR21Monoculture.FirstChoiceDecomposition
import KR21Monoculture.Payoff
import AppliedModelingLib.Foundations.Math.EpsilonContinuity
import AppliedModelingLib.Foundations.Math.IntervalCrossing

open AppliedModelingLib

namespace KR21Monoculture
namespace AccuracyFamily

/-!
# Theorem 1 Payoff Bridge

This file formalizes the game-theoretic core of paper Theorem 1.  The remaining
analytic task is to instantiate the crossing certificate from Definition 1's
differentiability/asymptotic-optimality/monotonicity assumptions.
-/

/--
Paper proof notation:

`f(θA) = UA(θA, θH) + UAA(θA, θH)`.

This is the random-order payoff numerator for using the algorithm when the
opponent also uses the algorithm.
-/
noncomputable def theorem1_f {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.algorithm +
    Model.secondMoverEU M Strategy.algorithm Strategy.algorithm

/--
Paper proof notation:

`g(θA) = UH(θA, θH) + UAH(θA, θH)`.

This is the random-order payoff numerator for using a human evaluator when the
opponent uses the algorithm.
-/
noncomputable def theorem1_g {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.human +
    Model.secondMoverEU M Strategy.algorithm Strategy.human

/--
Paper proof notation:

`h(θA) = UH(θA, θH) + UHH(θA, θH)`.

This is both the all-human welfare expression and the payoff numerator for using
a human evaluator when the opponent also uses a human evaluator.
-/
noncomputable def theorem1_h {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.human +
    Model.secondMoverEU M Strategy.human Strategy.human

/--
The second strict-dominance numerator in the paper:

`UA(θA, θH) + UHA(θA, θH)`.
-/
noncomputable def theorem1_algorithmAgainstHuman {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.algorithm +
    Model.secondMoverEU M Strategy.human Strategy.algorithm

/--
Expected value of the best candidate remaining under `μ` after a fixed candidate
has already been removed.
-/
noncomputable def expectedBestAfterRemoval {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) : ℝ := pmfExp μ (fun π => value (bestRemainingAfter π c))

theorem expectedBestAfterRemoval_mul_value {n : ℕ}
    (μ : PMF (Ranking n)) (c0 : ℝ) (value : Candidate n → ℝ) (c : Candidate n) :
    expectedBestAfterRemoval μ (fun i => c0 * value i) c =
      c0 * expectedBestAfterRemoval μ value c := by
  unfold expectedBestAfterRemoval
  simp [pmfExp_const_mul]

/--
Removing candidate `c` lowers the top-choice value exactly on the first-choice
fiber of `c`, by the top-second value gap on that fiber.
-/
theorem expectedBestAfterRemoval_eq_firstMover_sub_firstChoiceGapMass {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) :
    expectedBestAfterRemoval μ value c =
      expectedFirstMoverUtility μ value - firstChoiceGapMass μ value c := by
  unfold expectedBestAfterRemoval expectedFirstMoverUtility firstChoiceGapMass
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass
  rw [← pmfExp_sub]
  congr 1
  funext π
  by_cases h : firstChoice π = c
  · subst c
    calc
      value (bestRemainingAfter π (firstChoice π)) = value (secondChoice π) := by
        simpa [firstChoice, secondChoice] using
          congrArg value (bestRemainingAfter_of_eq π)
      _ = value (firstChoice π) - valueGap value π := by
        simp [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
          firstChoice, secondChoice,
          AppliedModelingLib.SocialChoice.Ranking.firstChoice,
          AppliedModelingLib.SocialChoice.Ranking.secondChoice]
      _ = value (firstChoice π) -
          (if firstChoice π = AppliedModelingLib.SocialChoice.Ranking.firstChoice π
            then AppliedModelingLib.SocialChoice.Ranking.valueGap value π else 0) := by
        simp [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
          firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice]
  · have hc : c ≠ firstChoice π := by
      intro hc
      exact h hc.symm
    have hcraw : c ≠ π 0 := by
      simpa [firstChoice] using hc
    rw [bestRemainingAfter_of_ne π h]
    simp [hcraw]

/--
Second-mover utility can be read as first averaging, over the first mover's draw,
the second mover's expected best remaining candidate after that first choice is
removed.
-/
theorem expectedSecondMoverIndependent_eq_expect_bestAfterRemoval {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μFirst
        (fun σ => expectedBestAfterRemoval μSecond value (firstChoice σ)) := by
  unfold expectedSecondMoverIndependent expectedBestAfterRemoval
  rw [pmfPairExp_swap]
  rfl

/--
Changing only the first mover's ranking law changes second-mover utility by a
candidatewise first-choice-probability delta weighted by the second mover's
expected best remaining candidate after that candidate is removed.
-/
theorem expectedSecondMoverIndependent_sub_eq_sum_firstChoiceProb_sub_mul_bestAfterRemoval
    {n : ℕ} (μSecond μFirst₁ μFirst₂ : PMF (Ranking n))
    (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst₁ value -
        expectedSecondMoverIndependent μSecond μFirst₂ value =
      ∑ c : Candidate n,
        (firstChoiceProb μFirst₁ c - firstChoiceProb μFirst₂ c) *
          expectedBestAfterRemoval μSecond value c := by
  classical
  let U : Candidate n → ℝ := fun c => expectedBestAfterRemoval μSecond value c
  rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
  rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
  change expectedFirstMoverUtility μFirst₁ U - expectedFirstMoverUtility μFirst₂ U =
    ∑ c : Candidate n, (firstChoiceProb μFirst₁ c - firstChoiceProb μFirst₂ c) * U c
  rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb μFirst₁ U]
  rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb μFirst₂ U]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro c _
  ring

/-- In the paper's notation, `h(θA)` is constant as `θA` varies. -/
theorem theorem1_h_const {n : ℕ} (F : AccuracyFamily n) (θA θA' θH : ℝ) :
    theorem1_h F θA θH = theorem1_h F θA' θH := by
  simp [theorem1_h, modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist]

/-- `f(θA)` is exactly all-algorithm random-order welfare. -/
theorem theorem1_f_eq_algorithm_welfare {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) :
    theorem1_f F θA θH =
      Model.welfareRandomOrder (F.modelAt θA θH)
        Strategy.algorithm Strategy.algorithm := by
  rw [Model.welfareRandomOrder_self]
  rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU]
  rfl

/-- `h(θA)` is exactly all-human random-order welfare. -/
theorem theorem1_h_eq_human_welfare {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) :
    theorem1_h F θA θH =
      Model.welfareRandomOrder (F.modelAt θA θH)
        Strategy.human Strategy.human := by
  rw [Model.welfareRandomOrder_self]
  rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU]
  rfl

/-- Since `h(θA)` is constant in `θA`, it is epsilon-delta continuous. -/
theorem theorem1_h_epsilonContinuousAt {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ) :
    EpsilonContinuousAt (fun θA => theorem1_h F θA θH) θstar := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro θA hdist
  change |theorem1_h F θA θH - theorem1_h F θstar θH| < ε
  rw [theorem1_h_const F θA θstar θH]
  simpa using hε

/--
If every ranking atom of the accuracy family is epsilon-delta continuous at
`θstar`, then the paper's all-algorithm welfare expression `f` is continuous
there. This is the finite-probability bridge needed by the local nudge
certificate.
-/
theorem theorem1_f_epsilonContinuousAt_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar) :
    EpsilonContinuousAt (fun θA => theorem1_f F θA θH) θstar := by
  dsimp [theorem1_f, modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist, expectedFirstMoverUtility, expectedSecondMoverShared]
  exact epsilonContinuousAt_add
    (epsilonContinuousAt_pmfExp_of_atom
      (μ := fun θA => F.dist θA)
      (x := θstar)
      hdist
      (fun π => F.value (firstChoice π)))
    (epsilonContinuousAt_pmfExp_of_atom
      (μ := fun θA => F.dist θA)
      (x := θstar)
      hdist
      (fun π => F.value (secondChoice π)))

/--
Atomwise continuity of the ranking family also makes the paper's mixed
algorithm-human payoff expression `g` continuous in `θA`.
-/
theorem theorem1_g_epsilonContinuousAt_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar) :
    EpsilonContinuousAt (fun θA => theorem1_g F θA θH) θstar := by
  dsimp [theorem1_g, modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist, expectedFirstMoverUtility, expectedSecondMoverIndependent]
  exact epsilonContinuousAt_add
    (epsilonContinuousAt_const
      (pmfExp (F.dist θH) (fun π => F.value (firstChoice π))) θstar)
    (epsilonContinuousAt_pmfPairExp_right_of_atom
      (F.dist θH)
      (ν := fun θA => F.dist θA)
      (x := θstar)
      hdist
      (fun π σ => secondMoverUtility F.value π σ))

/-- Atomwise continuity makes the crossing function `f - g` continuous at a point. -/
theorem theorem1_f_sub_g_epsilonContinuousAt_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar) :
    EpsilonContinuousAt
      (fun θA => theorem1_f F θA θH - theorem1_g F θA θH) θstar :=
  epsilonContinuousAt_sub
    (theorem1_f_epsilonContinuousAt_of_atom_continuity F θH θstar hdist)
    (theorem1_g_epsilonContinuousAt_of_atom_continuity F θH θstar hdist)

/--
Atomwise continuity throughout an interval gives the `ContinuousOn` field needed
by the interval sign-change certificate for `f - g`.
-/
theorem theorem1_f_sub_g_continuousOn_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH lo hi : ℝ)
    (hdist :
      ∀ θA, θA ∈ Set.Icc lo hi →
        ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θA) :
    ContinuousOn
      (fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      (Set.Icc lo hi) :=
  continuousOn_of_forall_epsilonContinuousAt
    (fun θA hθA =>
      theorem1_f_sub_g_epsilonContinuousAt_of_atom_continuity
        F θH θA (hdist θA hθA))

/--
The paper's `f < h` persistence step follows from finite atomwise continuity of
the ranking law. This isolates the continuity part of the final nudge from the
separate one-sided crossing obligation `g < f`.
-/
theorem theorem1_f_lt_h_persists_right_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar)
    (hgap : theorem1_f F θstar θH < theorem1_h F θstar θH) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θA : ℝ, θstar < θA → θA < θstar + δ →
        theorem1_f F θA θH < theorem1_h F θA θH :=
  exists_right_radius_lt_of_epsilonContinuousAt
    (theorem1_f_epsilonContinuousAt_of_atom_continuity F θH θstar hdist)
    (theorem1_h_epsilonContinuousAt F θH θstar)
    hgap

/--
The local monotonicity consequences of Definition 1 used for inequality (5) in
the proof of Theorem 1.
-/
structure Theorem1MonotonicityAt {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) :
    Prop where
  firstMover_strict :
    Model.firstMoverEU (F.modelAt θA θH) Strategy.human <
      Model.firstMoverEU (F.modelAt θA θH) Strategy.algorithm
  secondMover_weak :
    Model.secondMoverEU (F.modelAt θA θH) Strategy.human Strategy.human ≤
      Model.secondMoverEU (F.modelAt θA θH) Strategy.human Strategy.algorithm

/--
The finite-removal form of Definition 1 monotonicity needed for inequality (5).
The first field is the strict `S = ∅` case; the second field is the weak
singleton-removal case, pointwise in the removed candidate.
-/
structure Theorem1RemovalMonotonicityAt {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) : Prop where
  firstMover_strict :
    expectedFirstMoverUtility (F.dist θH) F.value <
      expectedFirstMoverUtility (F.dist θA) F.value
  bestRemaining_weak :
    ∀ c : Candidate n,
      expectedBestAfterRemoval (F.dist θH) F.value c ≤
        expectedBestAfterRemoval (F.dist θA) F.value c

theorem theorem1RemovalMonotonicityAt_of_mul_value {n : ℕ}
    {F : AccuracyFamily n} {θA θH c0 : ℝ} (hc0 : 0 < c0)
    (hmono :
      Theorem1RemovalMonotonicityAt
        ({ dist := F.dist, value := fun i => c0 * F.value i } :
          AccuracyFamily n) θA θH) :
    Theorem1RemovalMonotonicityAt F θA θH := by
  constructor
  · have h := hmono.firstMover_strict
    simp [AppliedModelingLib.SocialChoice.Ranking.expectedFirstMoverUtility_mul_value] at h
    exact lt_of_mul_lt_mul_left h hc0.le
  · intro c
    have h := hmono.bestRemaining_weak c
    simp [expectedBestAfterRemoval_mul_value] at h
    exact le_of_mul_le_mul_left h hc0

/--
Definition 1's finite-removal monotonicity implies the local monotonicity
certificate used by Theorem 1.
-/
theorem theorem1MonotonicityAt_of_removalMonotonicity {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hmono : Theorem1RemovalMonotonicityAt F θA θH) :
    Theorem1MonotonicityAt F θA θH := by
  constructor
  · simpa [modelAt, Model.firstMoverEU, Model.rankingDist] using
      hmono.firstMover_strict
  · simp [modelAt, Model.secondMoverEU, Model.rankingDist]
    rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    exact pmfExp_le_pmfExp_of_forall_le
      (F.dist θH)
      (fun σ => expectedBestAfterRemoval (F.dist θH) F.value (firstChoice σ))
      (fun σ => expectedBestAfterRemoval (F.dist θA) F.value (firstChoice σ))
      (fun σ => hmono.bestRemaining_weak (firstChoice σ))

theorem value_le_centerFirst_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) (c : Candidate n) :
    value c ≤ value (firstChoice ρ) := by
  by_cases hc : c = firstChoice ρ
  · simp [hc]
  · exact le_of_lt (hvalue (rankOf_firstChoice_lt_rankOf_of_ne ρ hc))

theorem value_le_centerSecond_of_strictlyOrderedBy_of_ne_centerFirst {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) {c : Candidate n}
    (hc : c ≠ firstChoice ρ) :
    value c ≤ value (secondChoice ρ) := by
  by_cases hsecond : c = secondChoice ρ
  · simp [hsecond]
  · have hlt : rankOf ρ (secondChoice ρ) < rankOf ρ c := by
      simpa [rankOf, secondChoice] using
        one_lt_rankOf_of_ne_first_second ρ hc hsecond
    exact le_of_lt (hvalue hlt)

/--
If the algorithm were perfectly concentrated on the center ranking, then a
human first mover followed by that perfect algorithm has strictly lower total
payoff than the all-perfect-algorithm payoff.  This is the strict limiting gap
used in the Mallows asymptotic-first-dominance proof.
-/
theorem expected_human_against_pureCenter_lt_pureCenter_payoff {n : ℕ}
    (μ : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy ρ value)
    (hmass : 0 < (μ (swapTopTwo ρ)).toReal) :
    expectedFirstMoverUtility μ value +
        expectedSecondMoverIndependent μ (PMF.pure ρ) value <
      expectedFirstMoverUtility (PMF.pure ρ) value +
        expectedSecondMoverShared (PMF.pure ρ) value := by
  classical
  have hpoint :
      pmfExp μ
          (fun π =>
            value (firstChoice π) +
              value (bestRemainingAfter π (firstChoice ρ))) <
        value (firstChoice ρ) + value (secondChoice ρ) := by
    refine AppliedModelingLib.pmfExp_lt_of_forall_le_exists_lt μ
      (fun π =>
        value (firstChoice π) +
          value (bestRemainingAfter π (firstChoice ρ)))
      (value (firstChoice ρ) + value (secondChoice ρ)) ?hle ?hex
    · intro π
      exact add_le_add
        (value_le_centerFirst_of_strictlyOrderedBy hvalue (firstChoice π))
        (value_le_centerSecond_of_strictlyOrderedBy_of_ne_centerFirst
          hvalue (bestRemainingAfter_ne_removed π (firstChoice ρ)))
    · refine ⟨swapTopTwo ρ, hmass, ?_⟩
      have htop : value (secondChoice ρ) < value (firstChoice ρ) :=
        hvalue (rankOf_center_first_lt_second ρ)
      have hbest :
          bestRemainingAfter (swapTopTwo ρ) (firstChoice ρ) = secondChoice ρ := by
        rw [bestRemainingAfter_of_ne]
        · simpa using firstChoice_swapTopTwo ρ
        · exact swapTopTwo_firstChoice_ne ρ
      have hfirst :
          firstChoice (swapTopTwo ρ) = secondChoice ρ := by
        simpa using firstChoice_swapTopTwo ρ
      calc
        value (firstChoice (swapTopTwo ρ)) +
            value (bestRemainingAfter (swapTopTwo ρ) (firstChoice ρ))
            = value (secondChoice ρ) + value (secondChoice ρ) := by
              rw [hfirst, hbest]
        _ < value (firstChoice ρ) + value (secondChoice ρ) := by
              linarith
  have hleft :
      expectedFirstMoverUtility μ value +
          expectedSecondMoverIndependent μ (PMF.pure ρ) value =
        pmfExp μ
          (fun π =>
            value (firstChoice π) +
              value (bestRemainingAfter π (firstChoice ρ))) := by
    rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    simp [expectedFirstMoverUtility, expectedBestAfterRemoval, pmfExp_add]
  have hright :
      expectedFirstMoverUtility (PMF.pure ρ) value +
          expectedSecondMoverShared (PMF.pure ρ) value =
        value (firstChoice ρ) + value (secondChoice ρ) := by
    simp [expectedFirstMoverUtility, expectedSecondMoverShared]
  simpa [hleft, hright] using hpoint

/--
The strict pure-center payoff gap is stable under finite atomwise perturbations
of the algorithmic ranking law.  This generic form takes the limiting strict
gap as a proved premise, so concrete source routes can discharge it without
being forced through a particular positive-mass ranking witness.
-/
theorem exists_atomwise_radius_first_dominance_near_pureCenter_of_pure_gap {n : ℕ}
    (muH : PMF (Ranking n)) (rho : Ranking n) (value : Candidate n -> ℝ)
    (hpure :
      expectedFirstMoverUtility muH value +
          expectedSecondMoverIndependent muH (PMF.pure rho) value <
        expectedFirstMoverUtility (PMF.pure rho) value +
          expectedSecondMoverShared (PMF.pure rho) value) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ muA : PMF (Ranking n),
        (∀ pi : Ranking n,
          |(muA pi).toReal - ((PMF.pure rho : PMF (Ranking n)) pi).toReal| < delta) ->
          expectedFirstMoverUtility muH value +
              expectedSecondMoverIndependent muH muA value <
            expectedFirstMoverUtility muA value +
              expectedSecondMoverShared muA value := by
  classical
  let mu0 : PMF (Ranking n) := PMF.pure rho
  let G0 : ℝ :=
    expectedFirstMoverUtility muH value +
      expectedSecondMoverIndependent muH mu0 value
  let F0 : ℝ :=
    expectedFirstMoverUtility mu0 value +
      expectedSecondMoverShared mu0 value
  have hpure' : G0 < F0 := by
    simpa [G0, F0, mu0] using hpure
  let gap : ℝ := F0 - G0
  have hgap_pos : 0 < gap := sub_pos.mpr hpure'
  let epsilon : ℝ := gap / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  rcases exists_atomwise_radius_pmfExp_close mu0
      (fun sigma : Ranking n =>
        expectedBestAfterRemoval muH value (firstChoice sigma)) hepsilon with
    ⟨deltaInd, hdeltaInd_pos, hdeltaInd⟩
  rcases exists_atomwise_radius_pmfExp_close mu0
      (fun pi : Ranking n => value (firstChoice pi)) hepsilon with
    ⟨deltaFirst, hdeltaFirst_pos, hdeltaFirst⟩
  rcases exists_atomwise_radius_pmfExp_close mu0
      (fun pi : Ranking n => value (secondChoice pi)) hepsilon with
    ⟨deltaShared, hdeltaShared_pos, hdeltaShared⟩
  refine ⟨min deltaInd (min deltaFirst deltaShared),
    lt_min hdeltaInd_pos (lt_min hdeltaFirst_pos hdeltaShared_pos), ?_⟩
  intro muA hclose
  have hclose_ind :
      ∀ pi : Ranking n, |(muA pi).toReal - (mu0 pi).toReal| < deltaInd := by
    intro pi
    exact lt_of_lt_of_le (hclose pi) (min_le_left deltaInd (min deltaFirst deltaShared))
  have hclose_first :
      ∀ pi : Ranking n, |(muA pi).toReal - (mu0 pi).toReal| < deltaFirst := by
    intro pi
    exact lt_of_lt_of_le (hclose pi)
      (le_trans (min_le_right deltaInd (min deltaFirst deltaShared))
        (min_le_left deltaFirst deltaShared))
  have hclose_shared :
      ∀ pi : Ranking n, |(muA pi).toReal - (mu0 pi).toReal| < deltaShared := by
    intro pi
    exact lt_of_lt_of_le (hclose pi)
      (le_trans (min_le_right deltaInd (min deltaFirst deltaShared))
        (min_le_right deltaFirst deltaShared))
  have hind :
      |expectedSecondMoverIndependent muH muA value -
          expectedSecondMoverIndependent muH mu0 value| < epsilon := by
    simpa [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval] using
      hdeltaInd muA hclose_ind
  have hfirst :
      |expectedFirstMoverUtility muA value -
          expectedFirstMoverUtility mu0 value| < epsilon := by
    simpa [expectedFirstMoverUtility] using hdeltaFirst muA hclose_first
  have hshared :
      |expectedSecondMoverShared muA value -
          expectedSecondMoverShared mu0 value| < epsilon := by
    simpa [expectedSecondMoverShared] using hdeltaShared muA hclose_shared
  have hG :
      expectedFirstMoverUtility muH value +
          expectedSecondMoverIndependent muH muA value < G0 + epsilon := by
    have hind_upper := (abs_lt.mp hind).2
    dsimp [G0]
    linarith
  have hF :
      F0 - 2 * epsilon <
        expectedFirstMoverUtility muA value +
          expectedSecondMoverShared muA value := by
    have hfirst_lower := (abs_lt.mp hfirst).1
    have hshared_lower := (abs_lt.mp hshared).1
    dsimp [F0]
    linarith
  have hsep : G0 + epsilon < F0 - 2 * epsilon := by
    have hthree : 3 * epsilon < gap := by
      dsimp [epsilon]
      nlinarith [hgap_pos]
    dsimp [gap] at hthree
    linarith
  exact lt_trans hG (lt_trans hsep hF)

/--
The special positive-mass witness form of the finite stability bridge.  This
remains useful for concrete models that establish a swapped-top-two atom.
-/
theorem exists_atomwise_radius_first_dominance_near_pureCenter {n : ℕ}
    (μH : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy ρ value)
    (hmass : 0 < (μH (swapTopTwo ρ)).toReal) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ μA : PMF (Ranking n),
        (∀ π : Ranking n,
          |(μA π).toReal - ((PMF.pure ρ : PMF (Ranking n)) π).toReal| < δ) →
          expectedFirstMoverUtility μH value +
              expectedSecondMoverIndependent μH μA value <
            expectedFirstMoverUtility μA value +
              expectedSecondMoverShared μA value := by
  classical
  let μ0 : PMF (Ranking n) := PMF.pure ρ
  let G0 : ℝ :=
    expectedFirstMoverUtility μH value +
      expectedSecondMoverIndependent μH μ0 value
  let F0 : ℝ :=
    expectedFirstMoverUtility μ0 value +
      expectedSecondMoverShared μ0 value
  have hpure : G0 < F0 := by
    simpa [G0, F0, μ0] using
      expected_human_against_pureCenter_lt_pureCenter_payoff
        μH ρ value hvalue hmass
  let gap : ℝ := F0 - G0
  have hgap_pos : 0 < gap := sub_pos.mpr hpure
  let ε : ℝ := gap / 4
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases exists_atomwise_radius_pmfExp_close μ0
      (fun σ : Ranking n =>
        expectedBestAfterRemoval μH value (firstChoice σ)) hε with
    ⟨δind, hδind_pos, hδind⟩
  rcases exists_atomwise_radius_pmfExp_close μ0
      (fun π : Ranking n => value (firstChoice π)) hε with
    ⟨δfirst, hδfirst_pos, hδfirst⟩
  rcases exists_atomwise_radius_pmfExp_close μ0
      (fun π : Ranking n => value (secondChoice π)) hε with
    ⟨δshared, hδshared_pos, hδshared⟩
  refine ⟨min δind (min δfirst δshared),
    lt_min hδind_pos (lt_min hδfirst_pos hδshared_pos), ?_⟩
  intro μA hclose
  have hclose_ind :
      ∀ π : Ranking n, |(μA π).toReal - (μ0 π).toReal| < δind := by
    intro π
    exact lt_of_lt_of_le (hclose π) (min_le_left δind (min δfirst δshared))
  have hclose_first :
      ∀ π : Ranking n, |(μA π).toReal - (μ0 π).toReal| < δfirst := by
    intro π
    exact lt_of_lt_of_le (hclose π)
      (le_trans (min_le_right δind (min δfirst δshared))
        (min_le_left δfirst δshared))
  have hclose_shared :
      ∀ π : Ranking n, |(μA π).toReal - (μ0 π).toReal| < δshared := by
    intro π
    exact lt_of_lt_of_le (hclose π)
      (le_trans (min_le_right δind (min δfirst δshared))
        (min_le_right δfirst δshared))
  have hind :
      |expectedSecondMoverIndependent μH μA value -
          expectedSecondMoverIndependent μH μ0 value| < ε := by
    simpa [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval] using
      hδind μA hclose_ind
  have hfirst :
      |expectedFirstMoverUtility μA value -
          expectedFirstMoverUtility μ0 value| < ε := by
    simpa [expectedFirstMoverUtility] using hδfirst μA hclose_first
  have hshared :
      |expectedSecondMoverShared μA value -
          expectedSecondMoverShared μ0 value| < ε := by
    simpa [expectedSecondMoverShared] using hδshared μA hclose_shared
  have hG :
      expectedFirstMoverUtility μH value +
          expectedSecondMoverIndependent μH μA value < G0 + ε := by
    have hind_upper :=
      (abs_lt.mp hind).2
    dsimp [G0]
    linarith
  have hF :
      F0 - 2 * ε <
        expectedFirstMoverUtility μA value +
          expectedSecondMoverShared μA value := by
    have hfirst_lower :=
      (abs_lt.mp hfirst).1
    have hshared_lower :=
      (abs_lt.mp hshared).1
    dsimp [F0]
    linarith
  have hsep : G0 + ε < F0 - 2 * ε := by
    have hthree : 3 * ε < gap := by
      dsimp [ε]
      nlinarith [hgap_pos]
    dsimp [gap] at hthree
    linarith
  exact lt_trans hG (lt_trans hsep hF)

/--
The paper's final crossing state: after the initial equality point is nudged
upward, `g < f < h`, and monotonicity supplies the second dominance inequality.
-/
structure Theorem1CrossingCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θA : ℝ
  theta_gt : θH < θA
  first_dominance_crossing : theorem1_g F θA θH < theorem1_f F θA θH
  welfare_gap_persists : theorem1_f F θA θH < theorem1_h F θA θH
  monotonicity : Theorem1MonotonicityAt F θA θH

/--
The paper's final "slightly increase `θA`" step as a right-neighborhood
certificate.  It is designed to be instantiated later from continuity and the
chosen crossing point.
-/
structure Theorem1RightNudgeCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θstar : ℝ
  radius : ℝ
  thetaH_lt_star : θH < θstar
  radius_pos : 0 < radius
  between_on_right :
    ∀ θA, θstar < θA → θA < θstar + radius →
      theorem1_g F θA θH < theorem1_f F θA θH ∧
        theorem1_f F θA θH < theorem1_h F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
A local analytic certificate for the paper's final nudge. The `g < f` side is
given on a right interval after `θstar`; the `f < h` side is obtained from
epsilon-delta continuity of `f` and the strict inequality at `θstar`.
-/
structure Theorem1LocalNudgeCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θstar : ℝ
  gf_radius : ℝ
  thetaH_lt_star : θH < θstar
  gf_radius_pos : 0 < gf_radius
  f_epsilonContinuousAt :
    EpsilonContinuousAt (fun θA => theorem1_f F θA θH) θstar
  f_lt_h_at_star : theorem1_f F θstar θH < theorem1_h F θstar θH
  first_dominance_on_right :
    ∀ θA, θstar < θA → θA < θstar + gf_radius →
      theorem1_g F θA θH < theorem1_f F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
A local nudge certificate whose continuity field is stated at the finite PMF
atom level.  This is closer to Definition 1's family-level continuity premise
than asking directly for continuity of the already-aggregated payoff `f`.
-/
structure Theorem1AtomLocalNudgeCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  θstar : ℝ
  gf_radius : ℝ
  thetaH_lt_star : θH < θstar
  gf_radius_pos : 0 < gf_radius
  dist_atom_continuity :
    ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar
  f_lt_h_at_star : theorem1_f F θstar θH < theorem1_h F θstar θH
  first_dominance_on_right :
    ∀ θA, θstar < θA → θA < θstar + gf_radius →
      theorem1_g F θA θH < theorem1_f F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
An interval sign-change certificate for the paper's final nudge.  It replaces a
direct right-neighborhood `g < f` assumption with a compact-interval argument:
on `[lo, hi]`, `f - g` is continuous, starts nonpositive, and ends positive.
Lean then chooses the last nonpositive point.
-/
structure Theorem1SignChangeNudgeCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  lo : ℝ
  hi : ℝ
  thetaH_lt_lo : θH < lo
  lo_lt_hi : lo < hi
  diff_continuousOn :
    ContinuousOn (fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      (Set.Icc lo hi)
  nonpos_at_lo : theorem1_f F lo θH ≤ theorem1_g F lo θH
  positive_at_hi : theorem1_g F hi θH < theorem1_f F hi θH
  dist_atom_continuity :
    ∀ θA, lo ≤ θA → θA < hi →
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θA
  weaker_side :
    ∀ θA, θH < θA → θA < hi → theorem1_g F θA θH < theorem1_h F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
Paper-shaped interval certificate for the final Theorem 1 nudge.  Compared with
`Theorem1SignChangeNudgeCertificate`, this version asks for Definitions 2/3 as
`Model.PaperHypotheses` and for Definition 1 monotonicity in finite-removal
form; Lean fills the exact payoff fields.
-/
structure Theorem1IntervalAnalyticCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  lo : ℝ
  hi : ℝ
  thetaH_lt_lo : θH < lo
  lo_lt_hi : lo < hi
  diff_continuousOn :
    ContinuousOn (fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      (Set.Icc lo hi)
  nonpos_at_lo : theorem1_f F lo θH ≤ theorem1_g F lo θH
  positive_at_hi : theorem1_g F hi θH < theorem1_f F hi θH
  dist_atom_continuity :
    ∀ θA, lo ≤ θA → θA < hi →
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θA
  paper_hypotheses_on_interval :
    ∀ θA, θH < θA → θA < hi → Model.PaperHypotheses (F.modelAt θA θH)
  removal_monotonicity :
    ∀ θA, θH < θA → Theorem1RemovalMonotonicityAt F θA θH

/--
Global paper-shaped analytic assumptions for Theorem 1 at a fixed `θH`.

The final theorem below derives the interval certificate from these fields:
Definition 2 at equal accuracy, atomwise continuity of the finite ranking law,
asymptotic eventual `g < f`, Definition 3 above `θH`, and Definition 1
finite-removal monotonicity.
-/
structure Theorem1GlobalAnalyticCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  prefers_independent_at_equal : Model.PrefersIndependentReranking (F.dist θH) F.value
  dist_atom_continuity :
    ∀ θA, θH ≤ θA →
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θA
  asymptotic_first_dominance :
    ∀ lower, θH < lower →
      ∃ hi, lower < hi ∧ theorem1_g F hi θH < theorem1_f F hi θH
  paper_hypotheses_above :
    ∀ θA, θH < θA → Model.PaperHypotheses (F.modelAt θA θH)
  removal_monotonicity :
    ∀ θA, θH < θA → Theorem1RemovalMonotonicityAt F θA θH

/--
Paper Theorem 1 assumptions, stated in the order used by the proof.

This is the family-level statement closest to the paper's theorem: Definition 2
holds at every positive accuracy, Definition 3 holds for every strictly more
accurate algorithm, and the Definition 1 analytic inputs needed in the two-firm
proof hold at the relevant finite-discrete level.
-/
structure Theorem1PaperAssumptions {n : ℕ} (F : AccuracyFamily n) : Type where
  prefers_independent :
    ∀ θ, 0 < θ → Model.PrefersIndependentReranking (F.dist θ) F.value
  prefers_weaker_competition :
    ∀ θA θH, 0 < θH → θH < θA →
      Model.PrefersWeakerCompetition (F.dist θA) (F.dist θH) F.value
  dist_atom_continuity :
    ∀ θ, 0 < θ →
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ' => ((F.dist θ') π).toReal) θ
  asymptotic_first_dominance :
    ∀ θH lower, 0 < θH → θH < lower →
      ∃ hi, lower < hi ∧ theorem1_g F hi θH < theorem1_f F hi θH
  removal_monotonicity :
    ∀ θA θH, 0 < θH → θH < θA → Theorem1RemovalMonotonicityAt F θA θH

/--
The direct payoff certificate for Theorem 1's conclusion.
-/
structure Theorem1PayoffCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θA : ℝ
  theta_gt : θH < θA
  algorithm_beats_human_against_algorithm :
    theorem1_g F θA θH < theorem1_f F θA θH
  algorithm_beats_human_against_human :
    theorem1_h F θA θH < theorem1_algorithmAgainstHuman F θA θH
  human_welfare_beats_algorithm :
    theorem1_f F θA θH < theorem1_h F θA θH

/--
Monotonicity converts the paper's inequality (5) into the second strict
dominance comparison.
-/
theorem theorem1_algorithmAgainstHuman_gt_h_of_monotonicity {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hmono : Theorem1MonotonicityAt F θA θH) :
    theorem1_h F θA θH < theorem1_algorithmAgainstHuman F θA θH := by
  unfold theorem1_h theorem1_algorithmAgainstHuman
  linarith [hmono.firstMover_strict, hmono.secondMover_weak]

/--
The crossing certificate is exactly the paper's final `g < f < h` step plus the
monotonicity proof of inequality (5).
-/
def payoffCertificate_of_crossingCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1CrossingCertificate F θH) :
    Theorem1PayoffCertificate F θH where
  θA := cert.θA
  theta_gt := cert.theta_gt
  algorithm_beats_human_against_algorithm := cert.first_dominance_crossing
  algorithm_beats_human_against_human :=
    theorem1_algorithmAgainstHuman_gt_h_of_monotonicity
      F cert.θA θH cert.monotonicity
  human_welfare_beats_algorithm := cert.welfare_gap_persists

/--
The right-neighborhood version of the paper's nudge step supplies a concrete
crossing certificate by choosing the midpoint `θstar + radius / 2`.
-/
noncomputable def crossingCertificate_of_rightNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1RightNudgeCertificate F θH) :
    Theorem1CrossingCertificate F θH := by
  let θA := cert.θstar + cert.radius / 2
  have hhalf_pos : 0 < cert.radius / 2 := half_pos cert.radius_pos
  have hstar_lt : cert.θstar < θA := by
    dsimp [θA]
    linarith
  have hθ : θH < θA := cert.thetaH_lt_star.trans hstar_lt
  have hwithin : θA < cert.θstar + cert.radius := by
    dsimp [θA]
    linarith
  have hbetween := cert.between_on_right θA hstar_lt hwithin
  exact
    { θA := θA
      theta_gt := hθ
      first_dominance_crossing := hbetween.1
      welfare_gap_persists := hbetween.2
      monotonicity := cert.monotonicity θA hθ }

/--
A payoff certificate yields the fixed-parameter monoculture paradox.
-/
theorem hasKR21MonocultureParadox_of_payoffCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1PayoffCertificate F θH) :
    Model.HasKR21MonocultureParadox (F.modelAt cert.θA θH) := by
  constructor
  · unfold Model.AlgorithmStrictlyDominant
    constructor
    · simpa [theorem1_f, theorem1_g] using
        cert.algorithm_beats_human_against_algorithm
    · simpa [theorem1_h, theorem1_algorithmAgainstHuman] using
        cert.algorithm_beats_human_against_human
  · unfold Model.HumanProfileBeatsAlgorithmProfile
    rw [Model.welfareRandomOrder_self, Model.welfareRandomOrder_self]
    rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU,
      Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU]
    simpa [theorem1_f, theorem1_h] using cert.human_welfare_beats_algorithm

/--
Paper Theorem 1, conditional on the final crossing certificate.
-/
theorem theorem1Target_of_payoffCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1PayoffCertificate F θH) :
    Theorem1Target F θH :=  ⟨cert.θA, cert.theta_gt, hasKR21MonocultureParadox_of_payoffCertificate cert⟩

/--
Paper Theorem 1, conditional on the crossing certificate produced by the paper's
continuity/asymptotic-optimality argument.
-/
theorem theorem1Target_of_crossingCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1CrossingCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_payoffCertificate
    (payoffCertificate_of_crossingCertificate cert)

/--
Paper Theorem 1 from the right-neighborhood nudge certificate.
-/
theorem theorem1Target_of_rightNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1RightNudgeCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_crossingCertificate
    (crossingCertificate_of_rightNudgeCertificate cert)

/--
Paper Theorem 1 from the local analytic nudge certificate.
-/
theorem theorem1Target_of_localNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1LocalNudgeCertificate F θH) :
    Theorem1Target F θH := by
  rcases exists_right_radius_lt_of_epsilonContinuousAt
      cert.f_epsilonContinuousAt
      (theorem1_h_epsilonContinuousAt F θH cert.θstar)
      cert.f_lt_h_at_star with
    ⟨fh_radius, hfh_radius_pos, hfh⟩
  refine theorem1Target_of_rightNudgeCertificate ?_
  refine
    { θstar := cert.θstar
      radius := min cert.gf_radius fh_radius
      thetaH_lt_star := cert.thetaH_lt_star
      radius_pos := lt_min cert.gf_radius_pos hfh_radius_pos
      between_on_right := ?_
      monotonicity := cert.monotonicity }
  intro θA hstar hwithin
  have hgf_within : θA < cert.θstar + cert.gf_radius := by
    have hmin : min cert.gf_radius fh_radius ≤ cert.gf_radius :=
      min_le_left cert.gf_radius fh_radius
    linarith
  have hfh_within : θA < cert.θstar + fh_radius := by
    have hmin : min cert.gf_radius fh_radius ≤ fh_radius :=
      min_le_right cert.gf_radius fh_radius
    linarith
  exact ⟨cert.first_dominance_on_right θA hstar hgf_within,
    hfh θA hstar hfh_within⟩

/-- Convert atomwise continuity into the aggregated local nudge certificate. -/
def localNudgeCertificate_of_atomLocalNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1AtomLocalNudgeCertificate F θH) :
    Theorem1LocalNudgeCertificate F θH where
  θstar := cert.θstar
  gf_radius := cert.gf_radius
  thetaH_lt_star := cert.thetaH_lt_star
  gf_radius_pos := cert.gf_radius_pos
  f_epsilonContinuousAt :=
    theorem1_f_epsilonContinuousAt_of_atom_continuity
      F θH cert.θstar cert.dist_atom_continuity
  f_lt_h_at_star := cert.f_lt_h_at_star
  first_dominance_on_right := cert.first_dominance_on_right
  monotonicity := cert.monotonicity

/--
Paper Theorem 1 from the atomwise local analytic nudge certificate.
-/
theorem theorem1Target_of_atomLocalNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1AtomLocalNudgeCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_localNudgeCertificate
    (localNudgeCertificate_of_atomLocalNudgeCertificate cert)

/--
Paper Theorem 1 from an interval sign-change nudge certificate.

This formalizes the robust version of the paper's crossing step: choose the last
point in an interval where `f ≤ g`; immediately to its right, `g < f`, while
`f < h` follows from `f ≤ g < h` at that point and finite atomwise continuity.
-/
theorem theorem1Target_of_signChangeNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1SignChangeNudgeCertificate F θH) :
    Theorem1Target F θH := by
  have hlo_nonpos :
      theorem1_f F cert.lo θH - theorem1_g F cert.lo θH ≤ 0 := by
    linarith [cert.nonpos_at_lo]
  have hhi_pos :
      0 < theorem1_f F cert.hi θH - theorem1_g F cert.hi θH := by
    linarith [cert.positive_at_hi]
  rcases exists_last_nonpos_with_right_pos_on_Icc
      (d := fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      cert.lo_lt_hi cert.diff_continuousOn hlo_nonpos hhi_pos with
    ⟨θstar, hlo_star, hstar_hi, hdiff_nonpos, hright_pos⟩
  have hthetaH_star : θH < θstar := cert.thetaH_lt_lo.trans_le hlo_star
  have hgap : theorem1_f F θstar θH < theorem1_h F θstar θH := by
    have hfg : theorem1_f F θstar θH ≤ theorem1_g F θstar θH := by
      linarith [hdiff_nonpos]
    have hgh : theorem1_g F θstar θH < theorem1_h F θstar θH :=
      cert.weaker_side θstar hthetaH_star hstar_hi
    exact lt_of_le_of_lt hfg hgh
  refine theorem1Target_of_atomLocalNudgeCertificate ?_
  refine
    { θstar := θstar
      gf_radius := (cert.hi - θstar) / 2
      thetaH_lt_star := hthetaH_star
      gf_radius_pos := by linarith
      dist_atom_continuity := cert.dist_atom_continuity θstar hlo_star hstar_hi
      f_lt_h_at_star := hgap
      first_dominance_on_right := ?_
      monotonicity := cert.monotonicity }
  intro θA hstar_lt hwithin
  have hθA_le_hi : θA ≤ cert.hi := by
    linarith
  have hpos := hright_pos θA hstar_lt hθA_le_hi
  linarith

/--
Definition 3 gives `g(θA) < h(θA)` at any pair `θA > θH` where the induced model
satisfies the paper hypotheses.
-/
theorem theorem1_g_lt_h_of_prefersWeakerCompetition {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hweak :
      Model.PrefersWeakerCompetition (F.dist θA) (F.dist θH) F.value) :
    theorem1_g F θA θH < theorem1_h F θA θH := by
  unfold theorem1_g theorem1_h Model.PrefersWeakerCompetition
    AppliedModelingLib.SocialChoice.Ranking.PrefersWeakerCompetition at *
  simp [modelAt, Model.firstMoverEU, Model.secondMoverEU, Model.rankingDist] at *
  linarith

/--
Definition 3, read through `Model.PaperHypotheses`.
-/
theorem theorem1_g_lt_h_of_paperHypotheses {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θA θH)) :
    theorem1_g F θA θH < theorem1_h F θA θH := theorem1_g_lt_h_of_prefersWeakerCompetition F θA θH hpaper.2

/-- Convert the paper-shaped interval certificate into the direct sign-change certificate. -/
def signChangeNudgeCertificate_of_intervalAnalyticCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1IntervalAnalyticCertificate F θH) :
    Theorem1SignChangeNudgeCertificate F θH where
  lo := cert.lo
  hi := cert.hi
  thetaH_lt_lo := cert.thetaH_lt_lo
  lo_lt_hi := cert.lo_lt_hi
  diff_continuousOn := cert.diff_continuousOn
  nonpos_at_lo := cert.nonpos_at_lo
  positive_at_hi := cert.positive_at_hi
  dist_atom_continuity := cert.dist_atom_continuity
  weaker_side := fun θA hθ hhi =>
    theorem1_g_lt_h_of_paperHypotheses F θA θH
      (cert.paper_hypotheses_on_interval θA hθ hhi)
  monotonicity := fun θA hθ =>
    theorem1MonotonicityAt_of_removalMonotonicity F θA θH
      (cert.removal_monotonicity θA hθ)

/--
Paper Theorem 1 from the interval analytic certificate.
-/
theorem theorem1Target_of_intervalAnalyticCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1IntervalAnalyticCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_signChangeNudgeCertificate
    (signChangeNudgeCertificate_of_intervalAnalyticCertificate cert)

/--
Definition 2 supplies the initial strict inequality `f(θ) < g(θ)` when the
algorithm and human accuracies are equal.
-/
theorem theorem1_f_lt_g_of_prefersIndependent_equalAccuracy {n : ℕ}
    (F : AccuracyFamily n) (θ : ℝ)
    (hind : Model.PrefersIndependentReranking (F.dist θ) F.value) :
    theorem1_f F θ θ < theorem1_g F θ θ := by
  unfold theorem1_f theorem1_g Model.PrefersIndependentReranking
    AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking at *
  simp [modelAt, Model.firstMoverEU, Model.secondMoverEU, Model.rankingDist] at *
  linarith

/--
Definition 2, read through `Model.PaperHypotheses` at equal accuracies.
-/
theorem theorem1_f_lt_g_of_paperHypotheses_equalAccuracy {n : ℕ}
    (F : AccuracyFamily n) (θ : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θ θ)) :
    theorem1_f F θ θ < theorem1_g F θ θ := theorem1_f_lt_g_of_prefersIndependent_equalAccuracy F θ hpaper.1

/--
Definition 2 plus atomwise continuity gives a left interval endpoint strictly
above `θH` where the initial comparison `f < g` still holds.

This is the exact paper premise used at equal accuracies; it does not require
Definition 3 at `θA = θH`.
-/
theorem theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ)
    (hind : Model.PrefersIndependentReranking (F.dist θH) F.value)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θH) :
    ∃ lo : ℝ, θH < lo ∧ theorem1_f F lo θH < theorem1_g F lo θH := by
  have hlt : theorem1_f F θH θH < theorem1_g F θH θH :=
    theorem1_f_lt_g_of_prefersIndependent_equalAccuracy F θH hind
  rcases exists_right_radius_lt_of_epsilonContinuousAt
      (theorem1_f_epsilonContinuousAt_of_atom_continuity F θH θH hdist)
      (theorem1_g_epsilonContinuousAt_of_atom_continuity F θH θH hdist)
      hlt with
    ⟨δ, hδ_pos, hpersist⟩
  refine ⟨θH + δ / 2, ?_, ?_⟩
  · linarith
  · exact hpersist (θH + δ / 2) (by linarith) (by linarith)

/--
Definition 2 plus atomwise continuity gives a left interval endpoint strictly
above `θH` where the initial comparison `f < g` still holds.
-/
theorem theorem1_exists_right_initial_f_lt_g_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θH θH))
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θH) :
    ∃ lo : ℝ, θH < lo ∧ theorem1_f F lo θH < theorem1_g F lo θH :=
  theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity
    F θH hpaper.1 hdist

/--
Paper Theorem 1 from the global analytic certificate.

The proof constructs the left endpoint from Definition 2 and continuity, chooses
a later right endpoint from asymptotic dominance, then applies the interval
sign-change bridge.
-/
theorem theorem1Target_of_globalAnalyticCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1GlobalAnalyticCertificate F θH) :
    Theorem1Target F θH := by
  rcases theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity
      F θH cert.prefers_independent_at_equal
      (cert.dist_atom_continuity θH le_rfl) with
    ⟨lo, hθH_lo, hf_lt_g_lo⟩
  rcases cert.asymptotic_first_dominance lo hθH_lo with
    ⟨hi, hlo_hi, hg_lt_f_hi⟩
  refine theorem1Target_of_intervalAnalyticCertificate ?_
  refine
    { lo := lo
      hi := hi
      thetaH_lt_lo := hθH_lo
      lo_lt_hi := hlo_hi
      diff_continuousOn := ?_
      nonpos_at_lo := le_of_lt hf_lt_g_lo
      positive_at_hi := hg_lt_f_hi
      dist_atom_continuity := ?_
      paper_hypotheses_on_interval := ?_
      removal_monotonicity := cert.removal_monotonicity }
  · exact theorem1_f_sub_g_continuousOn_of_atom_continuity F θH lo hi
      (fun θA hθA =>
        cert.dist_atom_continuity θA
          (le_trans (le_of_lt hθH_lo) hθA.1))
  · intro θA hlo_θA hθA_hi
    exact cert.dist_atom_continuity θA (le_trans (le_of_lt hθH_lo) hlo_θA)
  · intro θA hθA hθA_hi
    exact cert.paper_hypotheses_above θA hθA

/--
The paper-level Theorem 1 assumptions imply the fixed-`θH` global analytic
certificate used by the constructive crossing proof.
-/
def globalAnalyticCertificate_of_paperAssumptions {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (hθH : 0 < θH) (assumptions : Theorem1PaperAssumptions F) :
    Theorem1GlobalAnalyticCertificate F θH where
  prefers_independent_at_equal := assumptions.prefers_independent θH hθH
  dist_atom_continuity := fun θA hθH_le =>
    assumptions.dist_atom_continuity θA (lt_of_lt_of_le hθH hθH_le)
  asymptotic_first_dominance := fun lower hθH_lower =>
    assumptions.asymptotic_first_dominance θH lower hθH hθH_lower
  paper_hypotheses_above := fun θA hθA =>
    ⟨assumptions.prefers_independent θA (lt_trans hθH hθA),
      assumptions.prefers_weaker_competition θA θH hθH hθA⟩
  removal_monotonicity := fun θA hθA =>
    assumptions.removal_monotonicity θA θH hθH hθA

/--
Paper Theorem 1 from paper-level assumptions.
-/
theorem theorem1Target_of_paperAssumptions {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (hθH : 0 < θH) (assumptions : Theorem1PaperAssumptions F) :
    Theorem1Target F θH :=
  theorem1Target_of_globalAnalyticCertificate
    (globalAnalyticCertificate_of_paperAssumptions hθH assumptions)

end AccuracyFamily
end KR21Monoculture

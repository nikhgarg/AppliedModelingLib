import KR21Monoculture.Definition2AsymptoticBridge
import KR21Monoculture.ConditionalForm
import AppliedModelingLib.SocialChoice.Ranking.SequentialPayoff

/-!
# Literal Definition 1 to Theorem 1 bridge

The source Definition 1 describes an accuracy family at the ranking-law level:
its atoms are continuous and differentiable at positive accuracies, the true
ranking atom converges to one at high accuracy, and expected best remaining
value improves for every nonempty remaining set, strictly for the full set.
The two-firm proof of Theorem 1 consumes only its full-set and
one-candidate-removal consequences, plus a high-accuracy `g < f` endpoint.

This module makes that reduction proposition-valued.  It does not accept a
`Theorem1PaperAssumptions`, Definition-1, or source-model certificate.  The
definition-2 and definition-3 premises remain direct caller obligations, and
every Definition-1 clause is a visible binder in the source-shaped endpoint.
-/

open AppliedModelingLib Filter
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/--
The literal full-remaining-set clause of Definition 1 contains the two
finite-removal facts used by the two-firm proof: strict full-set improvement
and weak improvement after deleting any one candidate.  The result is a
conjunction of those facts rather than a proof certificate.
-/
theorem theorem1RemovalMonotonicity_fields_of_literalFiniteRemoval
    {n : ℕ} {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (hweak :
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH) F.value remaining ≤
          expectedBestInSet (F.dist thetaA) F.value remaining)
    (hstrict :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    expectedFirstMoverUtility (F.dist thetaH) F.value <
      expectedFirstMoverUtility (F.dist thetaA) F.value ∧
    ∀ c : Candidate n,
      AccuracyFamily.expectedBestAfterRemoval (F.dist thetaH) F.value c ≤
        AccuracyFamily.expectedBestAfterRemoval (F.dist thetaA) F.value c := by
  constructor
  · simpa only [expectedBestInSet_univ] using hstrict
  · intro c
    have hremaining :
        (Finset.univ \ ({c} : Finset (Candidate n))).Nonempty := by
      by_cases hc : c = 0
      · refine ⟨1, ?_⟩
        simp [hc]
      · refine ⟨0, ?_⟩
        exact by simpa using (Ne.symm hc)
    simpa only [expectedBestInSet_univ_sdiff_singleton] using hweak _ hremaining

/--
For a finite PMF, the literal Definition-1 limit of the true-ranking atom to
one implies convergence of every ranking atom to the corresponding pure-center
mass.  This is a finite normalization argument: the total probability outside
the center is `1 - Pr[center]`, and every wrong atom is bounded by that total.
-/
theorem atomwise_tendsto_pure_of_center_atom_tendsto
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (mu : ℝ → PMF alpha) (center : alpha)
    (hcenter : Tendsto (fun theta => ((mu theta) center).toReal) atTop (nhds 1)) :
    ∀ a : alpha,
      Tendsto (fun theta => ((mu theta) a).toReal) atTop
        (nhds (((PMF.pure center : PMF alpha) a).toReal)) := by
  have hwrong_eq : ∀ theta : ℝ,
      AppliedModelingLib.pmfProb (mu theta) (fun a => a ≠ center) =
        1 - ((mu theta) center).toReal := by
    intro theta
    rw [← AppliedModelingLib.pmfProb_singleton (mu theta) center]
    simpa only [ne_eq, not_false_eq_true] using
      (AppliedModelingLib.pmfProb_compl (mu theta) (fun a => a = center))
  have hwrong_tendsto :
      Tendsto (fun theta => AppliedModelingLib.pmfProb (mu theta) (fun a => a ≠ center))
        atTop (nhds 0) := by
    rw [show (fun theta => AppliedModelingLib.pmfProb (mu theta) (fun a => a ≠ center)) =
      (fun theta => 1 - ((mu theta) center).toReal) by
        funext theta
        exact hwrong_eq theta]
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hconst.sub hcenter
  intro a
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ theta : ℝ in atTop,
      AppliedModelingLib.pmfProb (mu theta) (fun a => a ≠ center) < epsilon :=
    hwrong_tendsto.eventually (Iio_mem_nhds hepsilon)
  rcases Filter.eventually_atTop.1 hsmall with ⟨lower, hlower⟩
  refine ⟨lower, ?_⟩
  intro theta htheta
  rw [Real.dist_eq]
  exact AppliedModelingLib.atomwise_close_to_pure_of_wrong_prob_lt
    (mu theta) center hepsilon (hlower theta htheta) a

/--
Atomwise convergence to a strictly true center yields the high-accuracy
`g < f` endpoint needed by the Theorem 1 crossing argument.  The strict
pure-center gap is derived from the direct Definition-2 premise at the fixed
human accuracy; no positive-mass ranking or source-distribution witness is
silently added.
-/
theorem asymptotic_first_dominance_of_atomwise_tendsto_to_strict_center
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n)
    (hcenter : StrictlyOrderedBy center F.value)
    (hprefers_independent : ∀ theta, 0 < theta →
      Model.PrefersIndependentReranking (F.dist theta) F.value)
    (hatom_tendsto : ∀ pi : Ranking n,
      Tendsto (fun theta => ((F.dist theta) pi).toReal) atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal))) :
    ∀ thetaH lower, 0 < thetaH → thetaH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g F hi thetaH <
          AccuracyFamily.theorem1_f F hi thetaH := by
  intro thetaH lower hthetaH hlower
  have hpure :
      expectedFirstMoverUtility (F.dist thetaH) F.value +
          expectedSecondMoverIndependent (F.dist thetaH) (PMF.pure center) F.value <
        expectedFirstMoverUtility (PMF.pure center) F.value +
          expectedSecondMoverShared (PMF.pure center) F.value :=
    AccuracyFamily.expected_human_against_pureCenter_lt_pureCenter_payoff_of_prefersIndependent
      (F.dist thetaH) center F.value hcenter (hprefers_independent thetaH hthetaH)
  rcases AccuracyFamily.exists_atomwise_radius_first_dominance_near_pureCenter_of_pure_gap
      (F.dist thetaH) center F.value hpure with
    ⟨delta, hdelta_pos, hdelta⟩
  have hclose_all : ∀ᶠ theta : ℝ in atTop,
      ∀ pi : Ranking n,
        |((F.dist theta) pi).toReal - ((PMF.pure center : PMF (Ranking n)) pi).toReal| <
          delta := by
    rw [Filter.eventually_all]
    intro pi
    have hball := (hatom_tendsto pi).eventually
      (Metric.ball_mem_nhds _ hdelta_pos)
    simpa only [Metric.mem_ball, Real.dist_eq] using hball
  rcases (hclose_all.and (eventually_gt_atTop lower)).exists with
    ⟨hi, hclose, hlower_hi⟩
  refine ⟨hi, hlower_hi, ?_⟩
  have hmain := hdelta (F.dist hi) hclose
  simpa [AccuracyFamily.theorem1_g, AccuracyFamily.theorem1_f,
    AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist] using hmain

/--
Theorem 1 from a derived finite-atom form of Definition 1 and direct
utility-side Definition-2/3 premises.  This endpoint intentionally asks for
all atomwise limits, which is stronger in presentation than the source's
one-atom asymptotic-optimality clause.  Use
`theorem1Target_of_sourceDefinition1Definition2_fields` for the literal
source-shaped form.
-/
theorem theorem1Target_of_finiteAtomwiseDefinition1_fields
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hcenter : StrictlyOrderedBy center F.value)
    (hprefers_independent : ∀ theta, 0 < theta →
      Model.PrefersIndependentReranking (F.dist theta) F.value)
    (hprefers_weaker_competition : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Model.PrefersWeakerCompetition (F.dist thetaA) (F.dist thetaH) F.value)
    (hatom_continuity : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      EpsilonContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hatom_tendsto : ∀ pi : Ranking n,
      Tendsto (fun theta => ((F.dist theta) pi).toReal) atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal)))
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH) F.value remaining ≤
          expectedBestInSet (F.dist thetaA) F.value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    AccuracyFamily.Theorem1Target F thetaH := by
  apply AccuracyFamily.theorem1Target_of_paperAssumptions hthetaH
  refine
    { prefers_independent := hprefers_independent
      prefers_weaker_competition := hprefers_weaker_competition
      dist_atom_continuity := hatom_continuity
      asymptotic_first_dominance :=
        asymptotic_first_dominance_of_atomwise_tendsto_to_strict_center
          F center hcenter hprefers_independent hatom_tendsto
      removal_monotonicity := ?_ }
  intro thetaA thetaH hthetaH hthetaHA
  rcases theorem1RemovalMonotonicity_fields_of_literalFiniteRemoval
      (hremaining_weak thetaA thetaH hthetaH hthetaHA)
      (hfull_set_strict thetaA thetaH hthetaH hthetaHA) with
    ⟨hfirst, hremaining⟩
  exact ⟨hfirst, hremaining⟩

/--
The source-shaped finite-family Theorem 1 bridge.  Its Definition-1 premises
match the published clauses directly: continuity and differentiability of
every ranking atom at positive accuracy, convergence only of the true-ranking
atom to one, weak monotonicity for every nonempty remaining set, and strict
full-set improvement.  Finite PMF normalization derives the stronger all-atom
limit needed by the crossing argument.

Definition 2 is also displayed in its published conditional form.  The
positive disagreement-mass premise makes that conditional expectation
well-defined, and the existing exact conditional-gain equivalence derives the
utility-side independent-reranking condition internally.  Definition 3 is
kept as the direct caller-visible comparison consumed by the two-firm proof.
The differentiability premise is retained for source fidelity even though the
current finite crossing proof uses its continuity consequence instead.
-/
theorem theorem1Target_of_sourceDefinition1Definition2_fields
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hcenter : StrictlyOrderedBy center F.value)
    (hdefinition2 : ∀ theta, 0 < theta →
      0 < disagreementProb (F.dist theta) ∧
        0 < disagreementConditionalGain (F.dist theta) F.value)
    (hprefers_weaker_competition : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Model.PrefersWeakerCompetition (F.dist thetaA) (F.dist thetaH) F.value)
    (hatom_continuous : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hatom_differentiable : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hcenter_tendsto :
      Tendsto (fun theta => ((F.dist theta) center).toReal) atTop (nhds 1))
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH) F.value remaining ≤
          expectedBestInSet (F.dist thetaA) F.value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    AccuracyFamily.Theorem1Target F thetaH := by
  apply theorem1Target_of_finiteAtomwiseDefinition1_fields F center thetaH hthetaH hcenter
  · intro theta htheta
    exact
      (prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos
        (F.dist theta) F.value (hdefinition2 theta htheta).1).mpr
        (hdefinition2 theta htheta).2
  · exact hprefers_weaker_competition
  · intro theta htheta pi
    exact AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (hatom_continuous theta htheta pi)
  · exact atomwise_tendsto_pure_of_center_atom_tendsto F.dist center hcenter_tendsto
  · exact hremaining_weak
  · exact hfull_set_strict

end KR21Monoculture

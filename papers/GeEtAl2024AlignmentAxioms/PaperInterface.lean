import GeEtAl2024AlignmentAxioms.MainTheorems
import GeEtAl2024AlignmentAxioms.Assumptions
import GeEtAl2024AlignmentAxioms.LossBased
import GeEtAl2024AlignmentAxioms.MajorityLoss
import GeEtAl2024AlignmentAxioms.C1Impossibility
import GeEtAl2024AlignmentAxioms.C2Separability
import GeEtAl2024AlignmentAxioms.C4LinearKemeny
import GeEtAl2024AlignmentAxioms.C5ParetoKemeny
import GeEtAl2024AlignmentAxioms.C6LeximaxPlurality
import GeEtAl2024AlignmentAxioms.AppendixB

/-!
# Paper interface: Axioms for AI Alignment from Human Feedback

**Authoritative source.** Ge et al., NeurIPS 2024 published conference PDF.
The SHA-256-pinned PDF and its one-time text transcript are recorded in the
paper-local source record. The arXiv record is a discovery cross-check, not the
governing source.

Each named source result below has exactly one complete transparent `Spec`.
Definitions 2.1, 2.2, 4.1, 4.2, and C.1 are reviewed directly against their
actual reusable declarations (`ParetoOptimal`, `PairwiseMajorityConsistent`,
`MajorityConsistent`, `WinnerMonotonic`, and `RankingSeparability`); this file
does not duplicate them through reflexive equivalence wrappers.

The repaired Lemma 3.4--3.5 targets preserve the paper's final Theorem 3.1
conclusion while making the valid strict-cone and perturbation-gap statements
explicit. They do not assert the printed weak-half-space/open-set step.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/--
Source Definition 2.2 and its attached observations: PMC means returning the
feasible ranking that realizes every strict pairwise-majority comparison; a
PMC ranking need not exist, and when one exists it is unique.  Appendix B's
separate infeasibility example has its own source owner below.
-/
def definition2_2_pairwiseMajorityConsistencyAndConsequencesSpec : Prop :=
  (∀ (Voter : Type) [Fintype Voter] (n : ℕ)
      (feasible : Ranking n → Prop)
      (rule : LinearRankAggregationRule Voter n feasible),
      PairwiseMajorityConsistent feasible rule ↔
        ∀ profile majorityRanking,
          FeasibleProfile feasible profile → feasible majorityRanking →
            IsPairwiseMajorityRanking profile majorityRanking →
              rule.run profile = majorityRanking) ∧
    (¬ ∃ ranking : Ranking 7,
      IsPairwiseMajorityRanking c1ProfilePlus1 ranking) ∧
    (∀ (Voter : Type) [Fintype Voter] (n : ℕ)
      (profile : RankingProfile Voter n) (first second : Ranking n),
      IsPairwiseMajorityRanking profile first →
        IsPairwiseMajorityRanking profile second → first = second)

/--
Source Definition 3.1's complete standard-loss formulation. The source
restricts the loss to nonnegative values and evaluates every strict submitted
comparison at the score difference induced by a linear reward parameter. A
rule minimizes this objective when the infimum over parameters inducing its
output ranking equals the unrestricted infimum on every feasible profile.
-/
noncomputable def standardLossFormulationSpec
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n
      (LinearFeasibleRanking features)) : Prop := by
  classical
  let objective :
      RankingProfile Voter n → LinearRewardParameter dimension → ℝ :=
    fun profile parameter =>
      ∑ voter : Voter, ∑ pair : Candidate n × Candidate n,
        if StrictlyPrefers (profile voter) pair.1 pair.2 then
          loss
            (linearReward parameter features pair.2 -
              linearReward parameter features pair.1)
        else 0
  exact
    (∀ input, 0 ≤ loss input) ∧
      ∀ profile,
        FeasibleProfile (LinearFeasibleRanking features) profile →
          sInf
              (objective profile ''
                {parameter |
                  InducesRanking features parameter (rule.run profile)}) =
            sInf (Set.range (objective profile))

/--
The complete finite counterexample form of source Theorem 3.1. The two
disjuncts are the source's positive-input two-candidate construction and its
negative-input six-candidate construction.
-/
def theorem3_1_lossBasedImpossibilitySpec : Prop :=
  ∀ (loss : ℝ → ℝ),
    (∀ input, 0 ≤ loss input) →
      ((Monotone loss ∧ ConvexOn ℝ Set.univ loss) ∨ StrictConvexOn ℝ Set.univ loss) →
        sInf (Set.range loss) < loss 0 →
          ((∃ positiveInput : ℝ, 0 < positiveInput ∧ loss positiveInput < loss 0 ∧
              ∀ rule : LinearRankAggregationRule Unit 0
                (LinearFeasibleRanking positiveInputFeatures),
                IsStandardLossMinimizing positiveInputFeatures loss rule →
                  ¬ ParetoOptimal (LinearFeasibleRanking positiveInputFeatures) rule ∧
                    ¬ PairwiseMajorityConsistent
                      (LinearFeasibleRanking positiveInputFeatures) rule) ∨
            (∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
              ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
                ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
                  0 < majorityCount + minorityCount ∧
                    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
                      ∀ rule : LinearRankAggregationRule
                        (Fin (majorityCount + minorityCount)) 4
                        (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
                        IsStandardLossMinimizing
                            (sixCandidateCopyFeatures ε δ) loss rule →
                          ¬ ParetoOptimal
                              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                            ¬ PairwiseMajorityConsistent
                              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule))

/--
Source Lemma 3.2 in its negative-input proof context. The checked witness is
strictly below one, which in particular proves the source's stated
`p ∈ (1/2, 1]` conclusion.
-/
def lemma3_2_unconstrainedCoreSeparationSpec : Prop :=
  ∀ {loss : ℝ → ℝ} {negativeInput : ℝ},
    (∀ input, 0 ≤ loss input) →
      ((Monotone loss ∧ ConvexOn ℝ Set.univ loss) ∨ StrictConvexOn ℝ Set.univ loss) →
        negativeInput < 0 → loss negativeInput < loss 0 →
          ∃ p : ℚ, (1 / 2 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ 1 ∧
            ∃ A1 A2 : ℝ, A1 < A2 ∧ 0 < A2 ∧
              ∃ rewards, IsGlobalMinimizer
                (unconstrainedCoreLoss (weightedLoss (p : ℝ) loss)) rewards ∧
                ∀ rewards,
                  IsGlobalMinimizer
                      (unconstrainedCoreLoss (weightedLoss (p : ℝ) loss)) rewards →
                    rewards.1 > A2 ∧ rewards.2 ≤ A1

/-- Source-facing conditional optimizer transfer of Lemma 3.3. -/
def lemma3_3_coreMinimizersSpec : Prop :=
  ∀ {g : ℝ → ℝ} {A1 A2 : ℝ}, A1 < A2 →
    (∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards) →
    (∀ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards →
      rewards.1 > A2 ∧ rewards.2 ≤ A1) →
    ∃ A3 A4, 0 < A3 ∧ ∃ parameter, IsGlobalMinimizer (coreLoss g) parameter ∧
      ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
        parameter.1 > A3 ∧ parameter.2 < A4

/--
Corrected source-facing Lemma 3.4: the Lemma 3.3 coordinate bounds put every
zero-perturbation core minimizer in the strict cone that ranks the original
candidate above its copy for every positive perturbation.
-/
def lemma3_4_correctedCopyConeSpec : Prop :=
  ∀ {g : ℝ → ℝ} {A3 A4 δ : ℝ},
    0 < A3 → 0 < δ → δ * A4 - A3 < 0 →
      (∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
        A3 < parameter.1 ∧ parameter.2 < A4) →
        ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
          allCopiesBelowOriginalCone δ parameter

/--
Corrected source-instance form of Lemma 3.5. Under the strict Lemma 3.4 cone,
the literal six-candidate objective has a strict gap on the entire weak bad
half-space for every sufficiently small positive perturbation.
-/
def lemma3_5_correctedPerturbationGapSpec : Prop :=
  ∀ {loss : ℝ → ℝ} {negativeInput δ : ℝ} {weight : ℚ}
    {base : ℝ × ℝ},
    (1 / 2 : ℝ) < (weight : ℝ) → (weight : ℝ) < 1 →
      (∀ input, 0 ≤ loss input) → ConvexOn ℝ Set.univ loss →
        negativeInput < 0 → loss negativeInput < loss 0 →
          IsGlobalMinimizer (coreLoss (weightedLoss (weight : ℝ) loss)) base →
            (∀ parameter,
              IsGlobalMinimizer (coreLoss (weightedLoss (weight : ℝ) loss)) parameter →
                copyBelowOriginalCone δ parameter) →
              ∃ bound radius : ℝ, 0 < bound ∧ 0 < radius ∧
                ∀ ε, 0 < ε → ε < radius →
                  sInf (sixCandidateSourceObjective ε δ (weight : ℝ) loss ''
                    { parameter |
                      linearReward (twoCoordinateParameter parameter)
                          (sixCandidateCopyFeatures ε δ) (5 : Candidate 4) ≤
                        linearReward (twoCoordinateParameter parameter)
                          (sixCandidateCopyFeatures ε δ) (4 : Candidate 4) }) >
                    sInf (Set.range
                      (sixCandidateSourceObjective ε δ (weight : ℝ) loss))

/-- Source-facing finite endpoint for Theorem 3.6 and Appendix A.5. -/
def theorem3_6_majorityLossSpec : Prop :=
  ∀ {Voter : Type} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features)),
      (∀ input, 0 ≤ loss input) → Monotone loss →
        loss 0 > sInf (Set.range loss) →
          IsMajorityLossMinimizing features loss rule →
            PairwiseMajorityConsistent (LinearFeasibleRanking features) rule

/--
Source Theorem 3.7 together with all mathematical clauses in its following
paragraph.  The first conjunct is the exact finite Appendix-A.6 impossibility;
the next two prove C1-plus-PO implies PMC and that an existing PMC ranking
respects every unanimous comparison.  The final conjunct records the corrected
fact about the Appendix-A.6 profile: its majority relation is cyclic, so it has
no PMC ranking.  Appendix B separately supplies the paper's infeasible-PMC
example.
-/
def theorem3_7_C1FailsParetoAndConsequencesSpec : Prop :=
  (∀ rule : LinearRankAggregationRule (Fin 5) 7
      (LinearFeasibleRanking c1Features),
      C1LinearRankAggregationRule (LinearFeasibleRanking c1Features) rule →
        ¬ ParetoOptimal (LinearFeasibleRanking c1Features) rule) ∧
    (∀ (Voter : Type) [Fintype Voter] (n : ℕ)
      (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible),
      C1LinearRankAggregationRule feasible rule → ParetoOptimal feasible rule →
        PairwiseMajorityConsistent feasible rule) ∧
    (∀ (Voter : Type) [Fintype Voter] [Nonempty Voter] (n : ℕ)
      (profile : RankingProfile Voter n) (ranking : Ranking n),
      IsPairwiseMajorityRanking profile ranking →
        RespectsPareto profile ranking) ∧
    (¬ ∃ ranking : Ranking 7,
      IsPairwiseMajorityRanking c1ProfilePlus1 ranking)

/--
The fixed-tie finite LCPO construction satisfies all four components of source
Theorem 4.3. The candidate-index tie break is fixed independently of profile.
-/
def theorem4_3_constructedFixedTieLCPOSpec : Prop :=
  ∀ {Voter : Type} [Fintype Voter] [Nonempty Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback),
      ParetoOptimal feasible (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) ∧
        PairwiseMajorityConsistent feasible
          (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) ∧
          MajorityConsistent feasible
            (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) ∧
            WinnerMonotonic feasible
              (fixedTieLCPO (Voter := Voter) feasible fallback hfallback)

/-- The exact explicit unique-PMC-but-infeasible construction of Appendix B. -/
def appendixBExplicitInfeasiblePMCSpec : Prop :=
  FeasibleProfile (LinearFeasibleRanking appendixBFeatures) appendixBProfile ∧
    IsPairwiseMajorityRanking appendixBProfile appendixBPMCRanking ∧
    (∀ ranking, IsPairwiseMajorityRanking appendixBProfile ranking →
      ranking = appendixBPMCRanking) ∧
    ¬ LinearFeasibleRanking appendixBFeatures appendixBPMCRanking

/-- The two source branches of Appendix-C Theorem C.2. -/
def theoremC_2_copelandAndLCPOFailSeparabilitySpec : Prop :=
  (∀ rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible,
    IsConsistentlyTieBrokenCopelandSelector rule →
      ¬ RankingSeparability c2AllRankingsFeasible rule) ∧
  (∀ copelandRule lcpoRule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible,
    IsConsistentlyTieBrokenLCPOSelector copelandRule lcpoRule →
      ¬ RankingSeparability c2AllRankingsFeasible lcpoRule)

/-- The complete finite fixed-tie form of source Theorem C.3. -/
def theoremC_3_linearKemenySpec : Prop :=
  ∀ {n : ℕ} (feasible : Ranking n → Prop) (fallback : Ranking n)
    (hfallback : feasible fallback) (voterCount : ℕ),
      PairwiseMajorityConsistent feasible
        (canonicalKemenyRule feasible fallback hfallback voterCount) ∧
        RankingSeparability feasible (canonicalKemenyRule feasible fallback hfallback)

/-- The literal finite linear-Kemeny counterexample of source Theorem C.4. -/
def theoremC_4_linearKemenyFailsParetoAndMajorityConsistencySpec : Prop :=
  ∀ rule : LinearRankAggregationRule (Fin 6) 18 (LinearFeasibleRanking c4Features),
    IsKemenySelector (LinearFeasibleRanking c4Features) rule →
      ¬ ParetoOptimal (LinearFeasibleRanking c4Features) rule ∧
        ¬ MajorityConsistent (LinearFeasibleRanking c4Features) rule

/--
The literal Pareto-constrained Kemeny counterexample of source Theorem C.5.
The first-profile output is the source proof's explicit WLOG selection of
`v1`; no global tie-breaking rule is added.
-/
def theoremC_5_paretoKemenyFailsSeparabilityAndMajorityConsistencySpec : Prop :=
  ∀ rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features),
    IsParetoKemenySelector rule →
      (rule 6).run c4Profile = c4Ranking_v1 →
      ¬ RankingSeparability (LinearFeasibleRanking c4Features) rule ∧
        ¬ MajorityConsistent (LinearFeasibleRanking c4Features) (rule 9)

/-- The finite fixed-tie form of source Theorem C.6. -/
def theoremC_6_fixedTieLeximaxPluralitySpec : Prop :=
  ∀ {n : ℕ} (feasible : Ranking n → Prop)
    (rule : ∀ voterCount : ℕ, LinearRankAggregationRule (Fin voterCount) n feasible),
      (∀ voterCount : ℕ, IsFixedTieLeximaxPluralitySelector feasible (rule voterCount)) →
        (∀ voterCount : ℕ, MajorityConsistent feasible (rule voterCount)) ∧
          (∀ voterCount : ℕ, WinnerMonotonic feasible (rule voterCount)) ∧
            RankingSeparability feasible rule

end GeEtAl2024AlignmentAxioms

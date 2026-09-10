import LBG22StrategicRanking.PaperInterface

/-!
# Archival claims with counterexamples

These statements retain the unqualified archival assertions. Their
counterexamples distinguish the printed assertions from the approved
source-facing targets in PaperInterface.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Proposition 3.1: one-level pure randomization maximizes applicant
welfare among all finite policies; within the two-level class, welfare is
asserted to be nonincreasing in the cutoff. Both clauses concern actual
equilibria in one fixed primitive environment. -/
def ApplicantWelfareArchivalSpec : Prop :=
  ∀ (cost production skill tie : ℝ → ℝ) (rho : ℝ),
    RankingPrimitives cost production skill 0 → rho ∈ Ioo (0 : ℝ) 1 →
    DifferentiableOn ℝ cost (Ioi 0) → DifferentiableOn ℝ production (Ioi 0) →
    DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) →
    Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    (∃ pureEffort pureScore : ℝ → ℝ,
      RankingEquilibrium cost production skill tie 0
        (fun k => if k = 0 then 0 else 1) (sourcePureRandomizationReward rho)
        pureEffort pureScore ∧
      sourceFiniteApplicantWelfare cost pureEffort pureScore tie
        (fun _ : Fin 1 => 0) (sourcePureRandomizationReward rho) = rho ∧
      ∀ (n : ℕ) (cutoff reward : ℕ → ℝ) (effort score : ℝ → ℝ),
        FiniteAdmissionPolicy n cutoff reward rho →
        RankingEquilibrium cost production skill tie n cutoff reward effort score →
        sourceFiniteApplicantWelfare cost effort score tie
          (fun i : Fin (n + 1) => cutoff i) reward ≤
        sourceFiniteApplicantWelfare cost pureEffort pureScore tie
          (fun _ : Fin 1 => 0) (sourcePureRandomizationReward rho)) ∧
    ∀ effort score : ℝ → ℝ → ℝ,
      (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
        RankingEquilibrium cost production skill tie 1
          (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) →
      AntitoneOn (fun c => sourceFiniteApplicantWelfare cost (effort c) (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c))
        (Ioc (0 : ℝ) (1 - rho))

/-- Proposition 4.2: group-specific admission regions, a nonnegative welfare
gap, strict positivity throughout the common-admission region, and zero
gap under pure randomization. The strict clause is retained for refutation. -/
def EnvironmentWelfareArchivalSpec : Prop :=
  ∀ (cost production skill : ℝ → ℝ) (effort score tie : Bool × ℝ → ℝ)
    (rho c psiA psiB : ℝ),
    RankingPrimitives cost production skill 0 → rho ∈ Ioo (0 : ℝ) 1 →
    c ∈ Ioc (0 : ℝ) (1 - rho) → 0 < psiB → psiB < psiA →
    DifferentiableOn ℝ cost (Ioi 0) → DifferentiableOn ℝ production (Ioi 0) →
    DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) →
    Measurable tie → InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1} →
    EnvironmentEquilibrium cost production skill psiA psiB tie 1
      (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) effort score →
    (∀ group : Bool, ∀ᵐ t ∂unitRankMeasure,
      sourceTwoLevelReward rho c (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
        (tieBrokenRank sourceTwoGroupMeasure score tie (group, t))).val =
        if sourceGroupThreshold skill psiA psiB group c < t then rho / (1 - c) else 0) ∧
    (∀ᵐ t ∂unitRankMeasure,
      0 ≤ sourceActualGroupWelfareGap cost effort score tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ∧
      (sourceGroupThreshold skill psiA psiB false c < t →
        0 < sourceActualGroupWelfareGap cost effort score tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t)) ∧
    ∀ pureEffort pureScore : Bool × ℝ → ℝ,
      EnvironmentEquilibrium cost production skill psiA psiB tie 0
        (fun k => if k = 0 then 0 else 1) (fun _ => rho) pureEffort pureScore →
      ∀ᵐ t ∂unitRankMeasure, sourceActualGroupWelfareGap cost pureEffort pureScore tie
        (fun _ : Fin 1 => 0) (fun _ => rho) t = 0

/-- Proposition 4.3: at every feasible cutoff below the top disadvantaged
rank, the high-region welfare gap is asserted to have a strictly positive
cutoff derivative. Differentiation is within the feasible policy interval,
so its deterministic endpoint uses the feasible one-sided derivative. The
fixed environment and tie key are shared by the entire equilibrium family. -/
def WelfareGapDerivativeArchivalSpec : Prop :=
  ∀ (cost production skill : ℝ → ℝ) (effort score : ℝ → Bool × ℝ → ℝ)
    (tie : Bool × ℝ → ℝ) (rho psiA psiB : ℝ),
    RankingPrimitives cost production skill 0 → rho ∈ Ioo (0 : ℝ) 1 →
    0 < psiB → psiB < psiA →
    DifferentiableOn ℝ cost (Ioi 0) → DifferentiableOn ℝ production (Ioi 0) →
    DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) →
    Measurable tie → InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1} →
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      EnvironmentEquilibrium cost production skill psiA psiB tie 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) →
    ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      c ≤ sourceEnvironmentCDF skill psiA psiB (psiB * skill 1) →
      ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t →
        ∃ v : ℝ, 0 < v ∧
          HasDerivWithinAt (fun d => sourceActualGroupWelfareGap cost (effort d) (score d) tie
            (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t)
            v (Ioc (0 : ℝ) (1 - rho)) c

/-- Proposition B.1's printed strict index/reward equivalence. Even with
the continuum convention, this asks for the equivalence for every pair in
one full-measure applicant set; it is distinct from reward-band preservation. -/
def MultidimensionalRankArchivalSpec : Prop :=
  ∀ (m n : ℕ) (cost : ℝ → ℝ) (h rho : ℝ)
    (weight : Fin (m + 1) → ℝ) (skill : Fin (m + 1) → ℝ → ℝ)
    (cutoff reward : ℕ → ℝ) (effort : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (score tie : (Fin (m + 1) → ℝ) → ℝ),
    MultidimensionalPrimitives m cost h weight skill →
    FiniteAdmissionPolicy n cutoff reward rho →
    Measurable tie → InjOn tie {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1} →
    MultidimensionalEquilibrium m n cost h weight skill cutoff reward effort score tie →
    ∃ good : Set (Fin (m + 1) → ℝ),
      (∀ᵐ x ∂sourceMultidimensionalPopulation (Fin (m + 1)), x ∈ good) ∧
      ∀ x ∈ good, ∀ y ∈ good,
        (reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
          (tieBrokenRank (sourceMultidimensionalPopulation (Fin (m + 1))) score tie x)).val <
         reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
          (tieBrokenRank (sourceMultidimensionalPopulation (Fin (m + 1))) score tie y)).val ↔
         sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill x) <
         sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill y))

/-- Proposition B.2's universal supportability assertion for actual
equilibria. The school weight may vary with the target cutoff, while the
population, budget, primitives, and tie key remain fixed across policies. -/
def WeightedPrivateUtilityArchivalSpec : Prop :=
  ∀ (cost production skillM skillU : ℝ → ℝ) (B rho : ℝ)
    (effortM effortU score : ℝ → ℝ × ℝ → ℝ) (tie : ℝ × ℝ → ℝ),
    MultitaskPrimitives cost production skillM skillU B rho →
    Measurable tie → InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1 ∧ x.2 ∈ Ioc (0 : ℝ) 1} →
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      MultitaskEquilibrium cost production skillM B rho c (effortM c) (effortU c) (score c) tie) →
    ∀ c ∈ Ioo (0 : ℝ) (1 - rho), ∃ beta ∈ Ioo (0 : ℝ) 1,
      ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
        sourceActualMultitaskSchoolUtility unitRankMeasure production skillM skillU
          (effortM d) (effortU d) (score d) tie rho beta d ≤
        sourceActualMultitaskSchoolUtility unitRankMeasure production skillM skillU
          (effortM c) (effortU c) (score c) tie rho beta c

end LBG22StrategicRanking

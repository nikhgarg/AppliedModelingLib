import LBG22StrategicRanking.FiniteUniquenessPrimitiveRepairs
import LBG22StrategicRanking.EffortComparativeStaticsPrimitiveRepairs
import LBG22StrategicRanking.PopulationUtilityPrimitiveRepairs
import LBG22StrategicRanking.ThreeLevelPrimitiveRepairs
import LBG22StrategicRanking.SocietalUtilityPrimitiveRepairs
import LBG22StrategicRanking.EnvironmentPrimitiveRepairs
import LBG22StrategicRanking.AccessPrimitiveRepairs
import LBG22StrategicRanking.GroupWelfarePrimitiveRepairs
import LBG22StrategicRanking.MultidimensionalPrimitiveRepairs
import LBG22StrategicRanking.MultitaskPrimitiveRepairs
import LBG22StrategicRanking.OrderBoundaryEquilibrium
import LBG22StrategicRanking.UpperTailSkill

/-!
# Strategic ranking: source statements

Applicants have uniformly distributed skill ranks and choose nonnegative
effort. A fixed measurable injective tie key orders applicants with equal
scores, including at the actual admission boundary. Best response holds
outside one null applicant set, against every nonnegative deviation. The
strict-percentile definitions below are an equilibrium-equivalent
representation of this stated model, not a corrected admission rule:
`OrderBoundaryEquilibrium` proves the all-deviation equivalence for scalar,
multidimensional, and hard-budget actions.

The source's economic primitives and equilibrium definition are displayed
separately from its result specifications. Proof endpoints are in
`ProofInterface`.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Cost, production, and skill primitives of Section 2. The minimum-cost
effort is `baseline`, which need not be zero. -/
def RankingPrimitives (cost production skill : ℝ → ℝ) (baseline : ℝ) : Prop :=
  0 ≤ baseline ∧
  ContinuousOn cost (Ici 0) ∧ StrictConvexOn ℝ (Ici 0) cost ∧
  (∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) ∧ cost baseline = 0 ∧
  ContinuousOn production (Ici 0) ∧ StrictMonoOn production (Ici 0) ∧
  ConcaveOn ℝ (Ici 0) production ∧ 0 ≤ production 0 ∧
  ContinuousOn skill (Icc (0 : ℝ) 1) ∧
  StrictMonoOn skill (Icc (0 : ℝ) 1) ∧ 0 ≤ skill 0

/-- An admission schedule with `n + 1` distinct levels and expected capacity
`rho`. Cutoffs include both endpoints of the unit rank interval. -/
def FiniteAdmissionPolicy (n : ℕ) (cutoff reward : ℕ → ℝ) (rho : ℝ) : Prop :=
  StrictMonoOn cutoff (Icc (0 : ℕ) (n + 1)) ∧ cutoff 0 = 0 ∧ cutoff (n + 1) = 1 ∧
  StrictMonoOn reward (Icc (0 : ℕ) n) ∧ 0 ≤ reward 0 ∧ reward n ≤ 1 ∧
  rho ∈ Ioo (0 : ℝ) 1 ∧
  (∑ i : Fin (n + 1), (cutoff (i.val + 1) - cutoff i.val) * reward i.val) = rho

/-- The one-level pure-randomization schedule gives every applicant the
capacity probability, independently of rank. -/
def sourcePureRandomizationReward (rho : ℝ) (_level : ℕ) : ℝ := rho

/-- The non-randomized member of the two-level policy class admits the
highest-ranked capacity fraction with probability one. -/
def sourceDeterministicCutoff (rho : ℝ) : ℝ := 1 - rho

/-- Strict-percentile representation of Definition 2.1. Population ranks are
computed from actual scores and the fixed tie key; their law is not supplied
as a premise. `SourceProofs.rankingEquilibrium_scorePriority_iff` proves its
equivalence to the stated known-priority boundary model under the existing
source primitives. -/
def RankingEquilibrium (cost production skill tie : ℝ → ℝ)
    (n : ℕ) (cutoff reward : ℕ → ℝ) (effort score : ℝ → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ t ∂unitRankMeasure,
    SourceFiniteBestResponseAt cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)

/-- Definition 2.1 with the author's clarified score-first, publicly known
priority order at the admission boundary. Each applicant outside one fixed
null set compares every nonnegative effort deviation. -/
def RankingScorePriorityEquilibrium (cost production skill tie : ℝ → ℝ)
    (n : ℕ) (cutoff reward : ℕ → ℝ) (effort score : ℝ → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ t ∂unitRankMeasure,
    ScorePriorityBestResponseAt unitRankMeasure cost production skill score tie
      (fun i : Fin (n + 1) => cutoff i) reward t (effort t)

/-- Proposition 2.1: every equilibrium preserves admission rewards almost
everywhere. The tie key is fixed but otherwise arbitrary. -/
def RankPreservationSpec : Prop :=
  ∀ (cost production skill tie effort score : ℝ → ℝ) (baseline rho : ℝ)
    (n : ℕ) (cutoff reward : ℕ → ℝ),
    RankingPrimitives cost production skill baseline →
    FiniteAdmissionPolicy n cutoff reward rho →
    Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    RankingEquilibrium cost production skill tie n cutoff reward effort score →
    ∀ᵐ t ∂unitRankMeasure,
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank unitRankMeasure score tie t)).val =
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t).val

/-- Theorem 2.2: the recursive second-price effort formula is an equilibrium
and determines every equilibrium effort profile up to a null set. The
unit-cost effort cap and the induced uniform rank law are conclusions. -/
def SecondPriceEffortSpec : Prop :=
  ∀ (cost production skill tie : ℝ → ℝ) (baseline rho : ℝ)
    (n : ℕ) (cutoff reward : ℕ → ℝ),
    RankingPrimitives cost production skill baseline →
    FiniteAdmissionPolicy n cutoff reward rho →
    Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    ∃ E : ℝ, 0 < E ∧ cost (baseline + E) = 1 ∧
      let effort := sourceFiniteBaselineEffort cost production skill baseline E n cutoff reward
      let score := sourceFiniteBaselineScore cost production skill baseline E n cutoff reward
      AEMeasurable effort unitRankMeasure ∧
      RankingEquilibrium cost production skill tie n cutoff reward effort score ∧
      Measure.map (tieBrokenRank unitRankMeasure score tie) unitRankMeasure = unitRankMeasure ∧
      (∀ᵐ t ∂unitRankMeasure,
        reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
          (tieBrokenRank unitRankMeasure score tie t)).val =
        reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) t).val) ∧
      ∀ otherEffort otherScore : ℝ → ℝ,
        RankingEquilibrium cost production skill tie n cutoff reward otherEffort otherScore →
        otherEffort =ᵐ[unitRankMeasure] effort

/-- Proposition 3.1: pure randomization maximizes welfare without extra
shape conditions. Two-level cutoff monotonicity additionally holds under
upper-tail log-skill concavity and geometric score-cost concavity. These
local conditions do not restrict the pure-randomization clause. -/
def ApplicantWelfareSpec : Prop :=
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
    ∀ E : ℝ, 0 < E → cost E = 1 →
      ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x => Real.log (skill (upperTailRank x))) →
      ConcaveOn ℝ {z | production 0 < Real.exp z ∧ Real.exp z ≤ production E}
        (fun z => Real.log (cost (effortIntervalInverse production E (Real.exp z)))) →
    ∀ effort score : ℝ → ℝ → ℝ,
      (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
        RankingEquilibrium cost production skill tie 1
          (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) →
      AntitoneOn (fun c => sourceFiniteApplicantWelfare cost (effort c) (score c) tie
        (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c))
        (Ioc (0 : ℝ) (1 - rho))

/-- Proposition 3.2: actual school utility is nondecreasing in the two-level
cutoff and is maximized at deterministic admission. The population, economic
primitives, and tie key are the same at every candidate policy. -/
def PrivateUtilitySpec : Prop :=
  ∀ (cost production skill tie : ℝ → ℝ) (effort score : ℝ → ℝ → ℝ) (rho : ℝ),
    RankingPrimitives cost production skill 0 → rho ∈ Ioo (0 : ℝ) 1 →
    DifferentiableOn ℝ cost (Ioi 0) → DifferentiableOn ℝ production (Ioi 0) →
    DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) →
    Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      RankingEquilibrium cost production skill tie 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) →
    MonotoneOn (fun c => sourceActualTwoLevelSchoolUtility (score c) tie rho c)
      (Ioc (0 : ℝ) (1 - rho)) ∧
    ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      sourceActualTwoLevelSchoolUtility (score c) tie rho c ≤
      sourceActualTwoLevelSchoolUtility (score (sourceDeterministicCutoff rho))
        tie rho (sourceDeterministicCutoff rho)

/-- Proposition 3.3: there is a source-admissible setting and a three-level
policy whose equilibrium school utility exceeds deterministic admission at
the same capacity. The model primitives and both profiles are existential
witnesses, not fixed parametric assumptions on the statement. -/
def ThreeLevelImprovementSpec : Prop :=
  ∀ tie : ℝ → ℝ, Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    ∃ (cost production skill : ℝ → ℝ) (rho : ℝ) (cutoff reward : ℕ → ℝ)
      (effort score deterministicEffort deterministicScore : ℝ → ℝ),
      RankingPrimitives cost production skill 0 ∧
      DifferentiableOn ℝ cost (Ioi 0) ∧ DifferentiableOn ℝ production (Ioi 0) ∧
      DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) ∧
      FiniteAdmissionPolicy 2 cutoff reward rho ∧
      RankingEquilibrium cost production skill tie 2 cutoff reward effort score ∧
      RankingEquilibrium cost production skill tie 1
        (sourceTwoLevelCutoff (sourceDeterministicCutoff rho))
        (sourceTwoLevelReward rho (sourceDeterministicCutoff rho))
        deterministicEffort deterministicScore ∧
      sourceFiniteSchoolUtility deterministicScore tie
        (fun i : Fin 2 => sourceTwoLevelCutoff (sourceDeterministicCutoff rho) i)
        (sourceTwoLevelReward rho (sourceDeterministicCutoff rho)) <
      sourceFiniteSchoolUtility score tie (fun i : Fin 3 => cutoff i) reward

/-- Proposition 3.4: in some setting, an interior two-level cutoff maximizes
population score. The actual equilibrium family shares one population and
tie key, and its admission mass is the fixed capacity at every cutoff. -/
def SocietalUtilitySpec : Prop :=
  ∀ tie : ℝ → ℝ, Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    ∃ (cost production skill : ℝ → ℝ) (rho cStar : ℝ) (effort score : ℝ → ℝ → ℝ),
      RankingPrimitives cost production skill 0 ∧
      DifferentiableOn ℝ cost (Ioi 0) ∧ DifferentiableOn ℝ production (Ioi 0) ∧
      DifferentiableOn ℝ skill (Ioo (0 : ℝ) 1) ∧
      rho ∈ Ioo (0 : ℝ) 1 ∧ cStar ∈ Ioo 0 (1 - rho) ∧
      rho / (1 - cStar) ∈ Ioo rho 1 ∧
      (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
        RankingEquilibrium cost production skill tie 1
          (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c) ∧
        (∫ t, sourceTwoLevelReward rho c
          (finiteLowerRankBand (fun i : Fin 2 => sourceTwoLevelCutoff c i)
            (tieBrokenRank unitRankMeasure (score c) tie t)).val ∂unitRankMeasure) = rho) ∧
      ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
        Integrable (score c) unitRankMeasure ∧
        sourceSocietalUtility (score c) ≤ sourceSocietalUtility (score cStar)

/-- The group-dependent equilibrium definition of Section 4. Both groups
face the same population ranking and differ only in their skill multiplier. -/
def EnvironmentEquilibrium (cost production skill : ℝ → ℝ) (psiA psiB : ℝ)
    (tie : Bool × ℝ → ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ)
    (effort score : Bool × ℝ → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ x ∂sourceTwoGroupMeasure,
    SourcePopulationFiniteBestResponseAt sourceTwoGroupMeasure cost production
      (sourceEnvironmentSkill skill psiA psiB) score tie
      (fun i : Fin (n + 1) => cutoff i) reward x (effort x)

/-- The same two-group game with known score-priority boundary admission. -/
def EnvironmentScorePriorityEquilibrium (cost production skill : ℝ → ℝ) (psiA psiB : ℝ)
    (tie : Bool × ℝ → ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ)
    (effort score : Bool × ℝ → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ x ∂sourceTwoGroupMeasure,
    ScorePriorityBestResponseAt sourceTwoGroupMeasure cost production
      (sourceEnvironmentSkill skill psiA psiB) score tie
      (fun i : Fin (n + 1) => cutoff i) reward x (effort x)

/-- Proposition 4.1: the equal-weight mixture CDF defines an effective skill
rank whose rewards are preserved at every equilibrium. Inverses in the source
CDF formula include the constant tails outside each group's skill support. -/
def EnvironmentRankPreservationSpec : Prop :=
  ∀ (cost production skill : ℝ → ℝ) (effort score tie : Bool × ℝ → ℝ)
    (baseline rho psiA psiB : ℝ) (n : ℕ) (cutoff reward : ℕ → ℝ),
    RankingPrimitives cost production skill baseline →
    FiniteAdmissionPolicy n cutoff reward rho → 0 < psiB → psiB < psiA →
    Measurable tie → InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1} →
    EnvironmentEquilibrium cost production skill psiA psiB tie n cutoff reward effort score →
    (∀ z, sourceEnvironmentCDF skill psiA psiB z =
      (1 / 2 : ℝ) * sourceSkillCDF skill (z / psiA) +
      (1 / 2 : ℝ) * sourceSkillCDF skill (z / psiB)) ∧
    ∀ᵐ x ∂sourceTwoGroupMeasure,
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank sourceTwoGroupMeasure score tie x)).val =
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (sourceEnvironmentRank skill psiA psiB x)).val

/-- Proposition 4.2 under the clarified weak/strict interpretation.
The welfare gap is nonnegative and is strictly positive in the common
admission region exactly when disadvantaged effort is positive. -/
def EnvironmentWelfareSpec : Prop :=
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
        (0 < sourceActualGroupWelfareGap cost effort score tie
          (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ↔
          0 < effort (false, t)))) ∧
    ∀ pureEffort pureScore : Bool × ℝ → ℝ,
      EnvironmentEquilibrium cost production skill psiA psiB tie 0
        (fun k => if k = 0 then 0 else 1) (fun _ => rho) pureEffort pureScore →
      ∀ᵐ t ∂unitRankMeasure, sourceActualGroupWelfareGap cost pureEffort pureScore tie
        (fun _ : Fin 1 => 0) (fun _ => rho) t = 0

/-- Proposition 4.3 under finite weak/strict interpretation, with derivative
signs stated where a feasible derivative exists. Classical differentiability
at every cutoff is not asserted, including at mixture-support junctions. -/
def WelfareGapDerivativeSpec : Prop :=
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
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho), ∀ d ∈ Ioc (0 : ℝ) (1 - rho), c ≤ d →
      ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false d < t →
        sourceActualGroupWelfareGap cost (effort c) (score c) tie
            (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t ≤
          sourceActualGroupWelfareGap cost (effort d) (score d) tie
            (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t ∧
        (c < d → 0 < effort c (false, t) →
          sourceActualGroupWelfareGap cost (effort c) (score c) tie
              (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c) t <
            sourceActualGroupWelfareGap cost (effort d) (score d) tie
              (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t)) ∧
    ∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      ∀ᵐ t ∂unitRankMeasure, sourceGroupThreshold skill psiA psiB false c < t →
        ∀ v : ℝ, HasDerivWithinAt (fun d => sourceActualGroupWelfareGap cost (effort d) (score d) tie
          (fun i : Fin 2 => sourceTwoLevelCutoff d i) (sourceTwoLevelReward rho d) t)
          v (Ioc (0 : ℝ) (1 - rho)) c →
          0 ≤ v ∧ (0 < effort c (false, t) → 0 < v)

/-- Proposition 4.4: pure randomization gives strictly greater disadvantaged
access than any two-level policy. Convexity of the skill CDF on its support
additionally makes two-level access nonincreasing in the cutoff. -/
def AccessSpec : Prop :=
  ∀ (cost production skill : ℝ → ℝ) (effort score : ℝ → Bool × ℝ → ℝ)
    (tie : Bool × ℝ → ℝ) (baseline rho psiA psiB : ℝ),
    RankingPrimitives cost production skill baseline → rho ∈ Ioo (0 : ℝ) 1 →
    0 < psiB → psiB < psiA →
    Measurable tie → InjOn tie {x | x.2 ∈ Ioc (0 : ℝ) 1} →
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho),
      EnvironmentEquilibrium cost production skill psiA psiB tie 1
        (sourceTwoLevelCutoff c) (sourceTwoLevelReward rho c) (effort c) (score c)) →
    let pureAccess := sourceActualDisadvantagedAccess
      (fun x => production baseline * sourceEnvironmentSkill skill psiA psiB x)
      tie (fun _ : Fin 1 => 0) (fun _ => rho)
    let access := fun c => sourceActualDisadvantagedAccess (score c) tie
      (fun i : Fin 2 => sourceTwoLevelCutoff c i) (sourceTwoLevelReward rho c)
    pureAccess = rho ∧
    (∀ c ∈ Ioc (0 : ℝ) (1 - rho), access c < pureAccess) ∧
    (ConvexOn ℝ (Icc (skill 0) (skill 1)) (sourceSkillCDF skill) →
      AntitoneOn access (Ioc (0 : ℝ) (1 - rho)))

/-! ## Appendix and supplement statements -/

/-- Corollary A.1: a capacity-preserving transfer from reward `j` to reward
`k < j` leaves lower bands unchanged, increases effort in band `k`, and
decreases effort from `k + 1` through `j`. -/
def EffortComparativeStaticsSpec : Prop :=
  ∀ (cost production skill tie effort newEffort score newScore : ℝ → ℝ)
    (baseline rho : ℝ) (n k j : ℕ) (cutoff reward newReward : ℕ → ℝ),
    RankingPrimitives cost production skill baseline →
    FiniteAdmissionPolicy n cutoff reward rho →
    FiniteAdmissionPolicy n cutoff newReward rho →
    DifferentiableOn ℝ cost (Ioi 0) → DifferentiableOn ℝ production (Ioi 0) →
    k < j → j ≤ n → reward k < newReward k → newReward j < reward j →
    (∀ i ≤ n, i ≠ k → i ≠ j → newReward i = reward i) →
    Measurable tie → InjOn tie (Ioc (0 : ℝ) 1) →
    RankingEquilibrium cost production skill tie n cutoff reward effort score →
    RankingEquilibrium cost production skill tie n cutoff newReward newEffort newScore →
    ∀ᵐ t ∂unitRankMeasure,
      let i := (finiteLowerRankBand (fun l : Fin (n + 1) => cutoff l) t).val
      (i < k → newEffort t = effort t) ∧
      (i = k → effort t ≤ newEffort t) ∧
      (k < i → i ≤ j → newEffort t ≤ effort t)

/-- The supplemental remark on ties in pre-effort skill. Applicants are
labelled by their uniform skill ranks as in Section 2: almost every applicant
has a skill distinct from every differently ranked applicant, and every
strict skill interval between two applicant ranks has positive population
mass. Neither conclusion imposes a new distributional assumption. -/
def PreEffortSkillRegularitySpec : Prop :=
  ∀ skill : ℝ → ℝ,
    ContinuousOn skill (Icc (0 : ℝ) 1) → StrictMonoOn skill (Icc (0 : ℝ) 1) →
    (∀ᵐ t ∂unitRankMeasure, ∀ u ∈ Icc (0 : ℝ) 1, skill t = skill u → t = u) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s < t →
      0 < unitRankMeasure {u | skill s < skill u ∧ skill u < skill t}

/-- The linear multidimensional model: independent uniform coordinate ranks,
simplex school weights, and convex increasing cost of the endogenous total
effort. There is no fixed effort budget or restriction to one-coordinate
actions. -/
def MultidimensionalPrimitives (m : ℕ) (cost : ℝ → ℝ) (h : ℝ)
    (weight : Fin (m + 1) → ℝ) (skill : Fin (m + 1) → ℝ → ℝ) : Prop :=
  0 < h ∧ (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 ∧
  ContinuousOn cost (Ici 0) ∧ StrictMonoOn cost (Ici 0) ∧ ConvexOn ℝ (Ici 0) cost ∧
  (∀ i, ContinuousOn (skill i) (Icc (0 : ℝ) 1)) ∧
  (∀ i, StrictMonoOn (skill i) (Icc (0 : ℝ) 1)) ∧ (∀ i, 0 ≤ skill i 0)

/-- Equilibrium of the multidimensional game against every nonnegative
effort-vector deviation, under one fixed score distribution and tie key. -/
def MultidimensionalEquilibrium (m n : ℕ) (cost : ℝ → ℝ) (h : ℝ)
    (weight : Fin (m + 1) → ℝ) (skill : Fin (m + 1) → ℝ → ℝ)
    (cutoff reward : ℕ → ℝ) (effort : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (score tie : (Fin (m + 1) → ℝ) → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin (m + 1)),
    SourceMultidimensionalBestResponseAt (sourceMultidimensionalPopulation (Fin (m + 1)))
      cost (sourceMultidimensionalCoefficient weight skill) score tie h
      (fun r => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i) r).val) x (effort x)

/-- The multidimensional game with known score-priority boundary admission
and all nonnegative vector deviations. -/
def MultidimensionalScorePriorityEquilibrium (m n : ℕ) (cost : ℝ → ℝ) (h : ℝ)
    (weight : Fin (m + 1) → ℝ) (skill : Fin (m + 1) → ℝ → ℝ)
    (cutoff reward : ℕ → ℝ) (effort : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (score tie : (Fin (m + 1) → ℝ) → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin (m + 1)),
    ScorePriorityMultidimensionalBestResponseAt (sourceMultidimensionalPopulation (Fin (m + 1)))
      cost (sourceMultidimensionalCoefficient weight skill) score tie h
      (fun i : Fin (n + 1) => cutoff i) reward x (effort x)

/-- Proposition B.1: the maximum weighted-skill index preserves reward
bands, and almost every applicant concentrates all effort on a maximizing
coordinate. Effort is endogenous and deviations range over all nonnegative vectors. -/
def MultidimensionalRankSpec : Prop :=
  ∀ (m n : ℕ) (cost : ℝ → ℝ) (h rho : ℝ)
    (weight : Fin (m + 1) → ℝ) (skill : Fin (m + 1) → ℝ → ℝ)
    (cutoff reward : ℕ → ℝ) (effort : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (score tie : (Fin (m + 1) → ℝ) → ℝ),
    MultidimensionalPrimitives m cost h weight skill →
    FiniteAdmissionPolicy n cutoff reward rho →
    Measurable tie → InjOn tie {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1} →
    MultidimensionalEquilibrium m n cost h weight skill cutoff reward effort score tie →
    ∀ᵐ x ∂sourceMultidimensionalPopulation (Fin (m + 1)),
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (tieBrokenRank (sourceMultidimensionalPopulation (Fin (m + 1))) score tie x)).val =
      reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
        (sourceMultidimensionalPreRank weight skill x)).val ∧
      ∃ best : Fin (m + 1), sourceMultidimensionalCoefficient weight skill x best =
          sourceCombinedSkill (sourceMultidimensionalCoefficient weight skill x) ∧
        ∀ i, effort x i = if i = best then ∑ j, effort x j else 0

/-- Primitive conditions of the two-task model. Technology assumptions are
on nonnegative efforts, and skill-quantile assumptions are on unit ranks.
No supporting weight, frontier curvature, affine skill, or budget sufficient
for the unconstrained scalar game is imposed. -/
def MultitaskPrimitives (cost production skillM skillU : ℝ → ℝ) (B rho : ℝ) : Prop :=
  0 < B ∧ rho ∈ Ioo (0 : ℝ) 1 ∧
  ContinuousOn cost (Ici 0) ∧ MonotoneOn cost (Ici 0) ∧ ConvexOn ℝ (Ici 0) cost ∧
  (∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) ∧
  ContinuousOn production (Ici 0) ∧ StrictMonoOn production (Ici 0) ∧
  ConcaveOn ℝ (Ici 0) production ∧ 0 ≤ production 0 ∧
  ContinuousOn skillM (Icc (0 : ℝ) 1) ∧ StrictMonoOn skillM (Icc (0 : ℝ) 1) ∧ 0 ≤ skillM 0 ∧
  ContinuousOn skillU (Icc (0 : ℝ) 1) ∧ StrictMonoOn skillU (Icc (0 : ℝ) 1) ∧ 0 ≤ skillU 0

/-- Both skill ranks are independent and uniform. Each applicant chooses a
nonnegative pair exhausting the source's fixed budget; measurable scores
alone determine admission. -/
def MultitaskEquilibrium (cost production skillM : ℝ → ℝ) (B rho c : ℝ)
    (effortM effortU score tie : ℝ × ℝ → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
    SourceHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure) cost production
      (fun x => skillM x.1) score tie B rho c x (effortM x) (effortU x)

/-- The independent-rank multitask game with a known score-priority boundary
and all feasible pairs at the same fixed budget. -/
def MultitaskScorePriorityEquilibrium (cost production skillM : ℝ → ℝ) (B rho c : ℝ)
    (effortM effortU score tie : ℝ × ℝ → ℝ) : Prop :=
  Measurable score ∧ ∀ᵐ x ∂unitRankMeasure.prod unitRankMeasure,
    ScorePriorityHardBudgetBestResponseAt (unitRankMeasure.prod unitRankMeasure) cost production
      (fun x => skillM x.1) score tie B rho c x (effortM x) (effortU x)

/-- Proposition B.2 under the affine-skill primitive curvature conditions.
The positive task weight is chosen before any equilibrium selection, and
supports the prescribed interior cutoff against every feasible two-level policy. -/
def WeightedPrivateUtilitySpec : Prop :=
  ∀ (cost production skillU : ℝ → ℝ) (B E rho lower width : ℝ) (tie : ℝ × ℝ → ℝ),
    RankingPrimitives cost production (fun t => lower + width * t) 0 →
    rho ∈ Ioo (0 : ℝ) 1 → 0 ≤ lower → 0 < width →
    0 < E → cost E = 1 → E ≤ B →
    ContinuousOn skillU (Icc (0 : ℝ) 1) → StrictMonoOn skillU (Icc (0 : ℝ) 1) →
    0 ≤ skillU 0 → production 0 = 0 →
    ConcaveOn ℝ (Ioo (0 : ℝ) B) (fun e => production e ^ 2) →
    ConvexOn ℝ (Icc (production (effortIntervalInverse cost E rho)) (production E))
      (fun x => x / cost (effortIntervalInverse production E x)) →
    DifferentiableOn ℝ cost (Ioo (0 : ℝ) E) →
    DifferentiableOn ℝ (deriv cost) (Ioo (0 : ℝ) E) →
    DifferentiableOn ℝ production (Ioo (0 : ℝ) B) →
    DifferentiableOn ℝ (deriv production) (Ioo (0 : ℝ) B) →
    ContinuousOn (deriv (deriv production)) (Ioo (0 : ℝ) B) →
    Measurable tie → InjOn tie {x | x.1 ∈ Ioc (0 : ℝ) 1 ∧ x.2 ∈ Ioc (0 : ℝ) 1} →
    ∀ c ∈ Ioo (0 : ℝ) (1 - rho), ∃ beta ∈ Ioo (0 : ℝ) 1,
      ∀ effortM effortU score : ℝ → ℝ × ℝ → ℝ,
        (∀ d ∈ Ioc (0 : ℝ) (1 - rho),
          MultitaskEquilibrium cost production (fun t => lower + width * t) B rho d
            (effortM d) (effortU d) (score d) tie) →
        ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
          sourceActualMultitaskSchoolUtility unitRankMeasure production
            (fun t => lower + width * t) skillU
            (effortM d) (effortU d) (score d) tie rho beta d ≤
          sourceActualMultitaskSchoolUtility unitRankMeasure production
            (fun t => lower + width * t) skillU
            (effortM c) (effortU c) (score c) tie rho beta c

/-- Lemma C.1: on one full-measure set of best responders, equal scores
receive equal rewards. This quantifies over every pair in that set, not just
almost every independent pair. -/
def EqualScoreRewardsSpec : Prop :=
  ∀ (cost production skill tie effort score : ℝ → ℝ) (baseline rho : ℝ)
    (n : ℕ) (cutoff reward : ℕ → ℝ),
    RankingPrimitives cost production skill baseline →
    FiniteAdmissionPolicy n cutoff reward rho →
    RankingEquilibrium cost production skill tie n cutoff reward effort score →
    ∃ good : Set ℝ, (∀ᵐ t ∂unitRankMeasure, t ∈ good) ∧
      ∀ x ∈ good, ∀ y ∈ good, score x = score y →
        reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
          (tieBrokenRank unitRankMeasure score tie x)).val =
        reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
          (tieBrokenRank unitRankMeasure score tie y)).val

/-- Lemma C.2: null changes to effort leave both the score law and every
counterfactual ranking reward unchanged, with the tie key fixed. -/
def NullDeviationsSpec : Prop :=
  ∀ (production skill tie effort deviatedEffort admission : ℝ → ℝ),
    effort =ᵐ[unitRankMeasure] deviatedEffort →
    let score := fun t => production (effort t) * skill t
    let deviatedScore := fun t => production (deviatedEffort t) * skill t
    Measure.map score unitRankMeasure = Measure.map deviatedScore unitRankMeasure ∧
    ∀ t v : ℝ,
      admission (counterfactualTieBrokenRank unitRankMeasure score tie t v) =
      admission (counterfactualTieBrokenRank unitRankMeasure deviatedScore tie t v)

/-- Lemma `order_p`: matching the two counterfactual rewards and imposing
the displayed incentive inequalities orders the two effort-cost increments. -/
def CostGapSpec : Prop :=
  ∀ (cost production skill score tie : ℝ → ℝ) (baseline rho : ℝ)
    (n : ℕ) (cutoff reward : ℕ → ℝ)
    (x y e eToHigh eHighToLow eHigh : ℝ),
    RankingPrimitives cost production skill baseline →
    FiniteAdmissionPolicy n cutoff reward rho →
    x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 → x < y →
    0 ≤ e → e < eToHigh → e < eHighToLow → eToHigh < eHigh → eHighToLow < eHigh →
    let R := fun t d => reward (finiteLowerRankBand (fun i : Fin (n + 1) => cutoff i)
      (counterfactualTieBrokenRank unitRankMeasure score tie t (production d * skill t))).val
    R y e = R x eHighToLow → R x eHigh = R y eToHigh →
    R y e - cost e ≥ R y eToHigh - cost eToHigh →
    R x eHigh - cost eHigh ≥ R x eHighToLow - cost eHighToLow →
    cost eHigh - cost eHighToLow ≤ cost eToHigh - cost e

/-- Lemma `order_g`: with matched endpoint scores, the lower-skill applicant
traverses the longer effort interval. Concavity is required only on the
source's nonnegative effort domain. -/
def ProductionGapSpec : Prop :=
  ∀ (cost production skill : ℝ → ℝ) (baseline x y e eToHigh eHighToLow eHigh : ℝ),
    RankingPrimitives cost production skill baseline →
    x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 → x < y →
    0 ≤ e → e < eToHigh → e < eHighToLow → eToHigh < eHigh → eHighToLow < eHigh →
    production e * skill y = production eHighToLow * skill x →
    production eHigh * skill x = production eToHigh * skill y →
    eToHigh - e < eHigh - eHighToLow

end LBG22StrategicRanking

import KR21Monoculture.AppendixBSmoothingStability
import AppliedModelingLib.Foundations.Math.IntervalCrossing
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Appendix B Gaussian-mixture source construction

This module supplies the measure-level part of the Appendix B smoothing
argument.  A fixed latent probability space first draws the finite iid
component labels and then independent standard Gaussian perturbations.  At
positive scale `s`, the resulting score coordinates are genuine finite
Gaussian mixtures centered at the source atoms.  At scale zero they reduce to
the exact discrete witnesses.

Keeping the latent measure fixed is important: atomwise continuity is proved
from almost-sure local constancy of the actual ranking map, not postulated as
an approximation property of a law named "Gaussian mixture".
-/

open AppliedModelingLib
open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace KR21Monoculture

noncomputable section

/-! ## Shared finite/product primitives -/

local instance : MeasurableSpace AppendixB1NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB1NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

abbrev AppendixB1NoiseTriple :=
  (AppendixB1NoiseAtom × AppendixB1NoiseAtom) × AppendixB1NoiseAtom

abbrev AppendixBGaussianTriple := ℝ × (ℝ × ℝ)

private theorem appendixB1NoiseWeight_nonneg_for_mixture
    (e : AppendixB1NoiseAtom) : 0 ≤ appendixB1NoiseWeight e := by
  cases e <;> norm_num [appendixB1NoiseWeight]

/-- The actual one-coordinate B.1 component-selection PMF. -/
noncomputable def appendixB1NoisePMF : PMF AppendixB1NoiseAtom :=
  AppliedModelingLib.finiteWeightedPMF
    appendixB1NoiseWeight appendixB1NoiseWeight_nonneg_for_mixture
    (by rw [appendixB1NoiseWeight_sum]; norm_num)

@[simp] theorem appendixB1NoisePMF_apply_toReal
    (e : AppendixB1NoiseAtom) :
    (appendixB1NoisePMF e).toReal = appendixB1NoiseWeight e := by
  rw [appendixB1NoisePMF,
    AppliedModelingLib.finiteWeightedPMF_apply_toReal]
  rw [appendixB1NoiseWeight_sum]
  simp

/-- Three independent B.1 component labels, one for each candidate. -/
noncomputable def appendixB1NoiseTriplePMF : PMF AppendixB1NoiseTriple :=
  AppliedModelingLib.pmfProd
    (AppliedModelingLib.pmfProd appendixB1NoisePMF appendixB1NoisePMF)
    appendixB1NoisePMF

/-- Three independent standard Gaussian perturbations. -/
noncomputable def appendixBStandardGaussianTripleMeasure :
    Measure AppendixBGaussianTriple :=
  (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance : IsProbabilityMeasure appendixBStandardGaussianTripleMeasure := by
  unfold appendixBStandardGaussianTripleMeasure
  infer_instance

/-- The fixed latent probability space for B.1 Gaussian smoothing. -/
noncomputable def appendixB1GaussianLatentMeasure :
    Measure (AppendixB1NoiseTriple × AppendixBGaussianTriple) :=
  appendixB1NoiseTriplePMF.toMeasure.prod appendixBStandardGaussianTripleMeasure

instance : IsProbabilityMeasure appendixB1GaussianLatentMeasure := by
  unfold appendixB1GaussianLatentMeasure
  infer_instance

/-- Interpret the three finite B.1 component labels as a candidate-indexed draw. -/
def appendixB1NoiseTripleFunction
    (noise : AppendixB1NoiseTriple) : Candidate 1 → AppendixB1NoiseAtom
  | 0 => noise.1.1
  | 1 => noise.1.2
  | _ => noise.2

/-- Interpret a three-real tuple as a candidate-indexed perturbation vector. -/
def appendixBGaussianTripleFunction
    (z : AppendixBGaussianTriple) : Candidate 1 → ℝ
  | 0 => z.1
  | 1 => z.2.1
  | _ => z.2.2

/-! ## Appendix B.1 actual Gaussian mixture -/

/-- B.1 realized scores with component standard deviation `|s|`. -/
def appendixB1GaussianMixtureScore
    (s : ℝ) (omega : AppendixB1NoiseTriple × AppendixBGaussianTriple)
    (c : Candidate 1) : ℝ :=
  appendixB1DiscreteScore (appendixB1NoiseTripleFunction omega.1) c +
    s * appendixBGaussianTripleFunction omega.2 c

theorem appendixB1GaussianMixtureScore_measurable
    (s : ℝ) (c : Candidate 1) :
    Measurable (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
      appendixB1GaussianMixtureScore s omega c) := by
  unfold appendixB1GaussianMixtureScore
  have hcenter : Measurable
      (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
        appendixB1DiscreteScore (appendixB1NoiseTripleFunction omega.1) c) :=
    (measurable_of_finite
      (fun noise : AppendixB1NoiseTriple =>
        appendixB1DiscreteScore (appendixB1NoiseTripleFunction noise) c)).comp
      measurable_fst
  have hperturb : Measurable
      (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
        appendixBGaussianTripleFunction omega.2 c) := by
    fin_cases c <;> simp [appendixBGaussianTripleFunction]
    · exact measurable_fst.comp measurable_snd
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact hcenter.add (measurable_const.mul hperturb)

/-- The ranking generated by the B.1 Gaussian-mixture score vector. -/
def appendixB1GaussianMixtureRank
    (s : ℝ) :
    (AppendixB1NoiseTriple × AppendixBGaussianTriple) → Ranking 1 :=
  fun omega =>
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (appendixB1GaussianMixtureScore s omega)

theorem appendixB1GaussianMixtureRank_measurable (s : ℝ) :
    Measurable (appendixB1GaussianMixtureRank s) := by
  unfold appendixB1GaussianMixtureRank
  exact AppliedModelingLib.SocialChoice.Ranking.measurable_rankByScore _
    (appendixB1GaussianMixtureScore_measurable s)

/-- The actual B.1 ranking PMF induced by the finite Gaussian mixture. -/
noncomputable def appendixB1GaussianMixtureRankingPMF (s : ℝ) :
    PMF (Ranking 1) :=
  rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
    (appendixB1GaussianMixtureRank s)
    (appendixB1GaussianMixtureRank_measurable s)

/-- The named Appendix-B ranking atom selected by a B.1 component triple. -/
def appendixB1DiscreteTripleAtom
    (noise : AppendixB1NoiseTriple) : AppendixBRankingAtom :=
  appendixBRankingAtomOfScores
    (appendixB1DiscreteScore (appendixB1NoiseTripleFunction noise) 0)
    (appendixB1DiscreteScore (appendixB1NoiseTripleFunction noise) 1)
    (appendixB1DiscreteScore (appendixB1NoiseTripleFunction noise) 2)

/-- The source's discrete B.1 ranking map on the finite component-label triple. -/
def appendixB1DiscreteTripleRank
    (noise : AppendixB1NoiseTriple) : Ranking 1 :=
  (appendixB1DiscreteTripleAtom noise).toRanking

theorem appendixB1DiscreteTripleRank_measurable :
    Measurable appendixB1DiscreteTripleRank :=
  measurable_of_finite _

theorem appendixB1DiscreteTripleAtom_toRanking
    (noise : AppendixB1NoiseTriple) :
    (appendixB1DiscreteTripleAtom noise).toRanking =
      appendixB1DiscreteTripleRank noise := by
  rfl

/-- A strictly score-decreasing enumeration is the canonical score ranking. -/
private theorem rankByScore_eq_of_strict_ranking_order
    {n : ℕ} (score : Candidate n → ℝ) (pi : Ranking n)
    (hstrict : ∀ i j : Candidate n, i < j → score (pi j) < score (pi i)) :
    AppliedModelingLib.SocialChoice.Ranking.rankByScore score = pi := by
  have hsort : pi = Tuple.sort (fun c : Candidate n => -score c) := by
    refine (Tuple.eq_sort_iff
      (f := fun c : Candidate n => -score c) (σ := pi)).mpr ?_
    constructor
    · intro i j hij
      rcases lt_or_eq_of_le hij with hij | rfl
      · have h := hstrict i j hij
        dsimp [Function.comp_def]
        linarith
      · rfl
    · intro i j hij heq
      exfalso
      have h := hstrict i j hij
      change -score (pi i) = -score (pi j) at heq
      linarith
  simpa [AppliedModelingLib.SocialChoice.Ranking.rankByScore] using hsort.symm

/-- For tie-free three-score vectors, the source classifier is the canonical ranking. -/
private theorem appendixBRankingAtom_rankByScore_eq_of_noTies
    (score : Candidate 1 → ℝ)
    (hnoTie : ∀ i j : Candidate 1, i ≠ j → score i ≠ score j) :
    (appendixBRankingAtomOfScores (score 0) (score 1) (score 2)).toRanking =
      AppliedModelingLib.SocialChoice.Ranking.rankByScore score := by
  classical
  by_cases htop : score 1 ≤ score 0 ∧ score 2 ≤ score 0
  · have h10 : score 1 < score 0 :=
      lt_of_le_of_ne htop.1 (hnoTie 1 0 (by decide))
    by_cases h21 : score 2 ≤ score 1
    · have h21' : score 2 < score 1 :=
        lt_of_le_of_ne h21 (hnoTie 2 1 (by decide))
      have hrank : AppliedModelingLib.SocialChoice.Ranking.rankByScore score =
          rum3Ranking012 := by
        apply rankByScore_eq_of_strict_ranking_order
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [rum3Ranking012]
        all_goals linarith
      simpa only [appendixBRankingAtomOfScores, if_pos htop, if_pos h21,
        AppendixBRankingAtom.toRanking] using hrank.symm
    · have h12 : score 1 < score 2 := lt_of_not_ge h21
      have h20 : score 2 < score 0 :=
        lt_of_le_of_ne htop.2 (hnoTie 2 0 (by decide))
      have hrank : AppliedModelingLib.SocialChoice.Ranking.rankByScore score =
          rum3Ranking021 := by
        apply rankByScore_eq_of_strict_ranking_order
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [rum3Ranking021]
      simpa only [appendixBRankingAtomOfScores, if_pos htop, if_neg h21,
        AppendixBRankingAtom.toRanking] using hrank.symm
  · by_cases hmiddle : score 0 < score 1 ∧ score 2 ≤ score 1
    · have h21 : score 2 < score 1 :=
        lt_of_le_of_ne hmiddle.2 (hnoTie 2 1 (by decide))
      by_cases h20 : score 2 ≤ score 0
      · have h20' : score 2 < score 0 :=
          lt_of_le_of_ne h20 (hnoTie 2 0 (by decide))
        have hrank : AppliedModelingLib.SocialChoice.Ranking.rankByScore score =
            rum3Ranking102 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [rum3Ranking102]
        simpa only [appendixBRankingAtomOfScores, if_neg htop,
          if_pos hmiddle, if_pos h20, AppendixBRankingAtom.toRanking] using hrank.symm
      · have h02 : score 0 < score 2 := lt_of_not_ge h20
        have hrank : AppliedModelingLib.SocialChoice.Ranking.rankByScore score =
            rum3Ranking120 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [rum3Ranking120]
        simpa only [appendixBRankingAtomOfScores, if_neg htop,
          if_pos hmiddle, if_neg h20, AppendixBRankingAtom.toRanking] using hrank.symm
    · by_cases h10 : score 1 ≤ score 0
      · have h10' : score 1 < score 0 :=
          lt_of_le_of_ne h10 (hnoTie 1 0 (by decide))
        have h20 : score 0 < score 2 := by
          apply lt_of_not_ge
          intro h20
          exact htop ⟨h10, h20⟩
        have hrank : AppliedModelingLib.SocialChoice.Ranking.rankByScore score =
            rum3Ranking201 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [rum3Ranking201]
          all_goals linarith
        simpa only [appendixBRankingAtomOfScores, if_neg htop,
          if_neg hmiddle, if_pos h10, AppendixBRankingAtom.toRanking] using hrank.symm
      · have h01 : score 0 < score 1 := lt_of_not_ge h10
        have h12 : score 1 < score 2 := by
          apply lt_of_not_ge
          intro h21
          exact hmiddle ⟨h01, h21⟩
        have hrank : AppliedModelingLib.SocialChoice.Ranking.rankByScore score =
            rum3Ranking210 := by
          apply rankByScore_eq_of_strict_ranking_order
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [rum3Ranking210]
          all_goals linarith
        simpa only [appendixBRankingAtomOfScores, if_neg htop,
          if_neg hmiddle, if_neg h10, AppendixBRankingAtom.toRanking] using hrank.symm

/-- At each source B.1 component triple, the canonical score rank is its displayed atom. -/
theorem appendixB1_rankByScore_discreteTriple_eq
    (noise : AppendixB1NoiseTriple) :
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB1DiscreteScore (appendixB1NoiseTripleFunction noise)) =
      appendixB1DiscreteTripleRank noise := by
  symm
  exact appendixBRankingAtom_rankByScore_eq_of_noTies
    (appendixB1DiscreteScore (appendixB1NoiseTripleFunction noise))
    (appendixB1_discreteScore_noTies (appendixB1NoiseTripleFunction noise))

theorem appendixB1GaussianMixtureRank_zero :
    appendixB1GaussianMixtureRank 0 =
      fun omega => appendixB1DiscreteTripleRank omega.1 := by
  funext omega
  unfold appendixB1GaussianMixtureRank appendixB1GaussianMixtureScore
  simpa using appendixB1_rankByScore_discreteTriple_eq omega.1

private theorem pmf_map_apply_toReal_fintype
    {α β : Type*} [Fintype α] [DecidableEq β]
    (law : PMF α) (f : α → β) (b : β) :
    ((law.map f) b).toReal =
      ∑ a : α, if b = f a then (law a).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : b = f a <;> simp [h]
  · intro a _
    by_cases h : b = f a
    · simpa [h] using law.apply_ne_top a
    · simp [h]

@[simp] private theorem appendixB1NoiseTriplePMF_apply_toReal
    (e0 e1 e2 : AppendixB1NoiseAtom) :
    (appendixB1NoiseTriplePMF ((e0, e1), e2)).toReal =
      appendixB1NoiseWeight e0 * appendixB1NoiseWeight e1 *
        appendixB1NoiseWeight e2 := by
  rw [appendixB1NoiseTriplePMF,
    AppliedModelingLib.pmfProd_apply_toReal,
    AppliedModelingLib.pmfProd_apply_toReal]
  simp [mul_assoc]

private theorem rankingPMFOfMeasure_from_finitePMF_eq_map
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : PMF α) (rank : α → Ranking 1) (hrank : Measurable rank) :
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
        law.toMeasure rank hrank = law.map rank := by
  apply PMF.ext
  intro pi
  apply (ENNReal.toReal_eq_toReal_iff'
    ((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
      law.toMeasure rank hrank).apply_ne_top pi)
    ((law.map rank).apply_ne_top pi)).mp
  rw [← PMF.toMeasure_apply_singleton
    (AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
      law.toMeasure rank hrank) pi MeasurableSet.of_discrete]
  rw [← PMF.toMeasure_apply_singleton (law.map rank) pi
    MeasurableSet.of_discrete]
  unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
  rw [Measure.toPMF_toMeasure]
  rw [PMF.toMeasure_map rank law hrank]

/-- The finite component product pushes forward to the exact B.1 atom table. -/
theorem appendixB1NoiseTriplePMF_map_discreteTripleAtom :
    appendixB1NoiseTriplePMF.map appendixB1DiscreteTripleAtom =
      appendixB1AtomPMF := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff'
    ((appendixB1NoiseTriplePMF.map appendixB1DiscreteTripleAtom).apply_ne_top a)
    (appendixB1AtomPMF.apply_ne_top a)).mp
  rw [pmf_map_apply_toReal_fintype]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [appendixB1AtomPMF,
    AppliedModelingLib.finiteWeightedPMF_apply_toReal,
    appendixB1RankingWeight_sum]
  simp only [div_one]
  rw [appendixB1RankingWeight_eq_iid_rum_pushforward]
  simp [appendixB1IIDRUMRankingWeight, appendixB1DiscreteTripleAtom,
    appendixB1DiscreteScore, appendixB1NoiseTripleFunction,
    appendixB1Value, eq_comm]

/-- The finite B.1 component product induces exactly the checked ranking PMF. -/
theorem appendixB1NoiseTriplePMF_map_discreteTripleRank :
    appendixB1NoiseTriplePMF.map appendixB1DiscreteTripleRank =
      appendixB1RankingPMF := by
  unfold appendixB1RankingPMF
  rw [← appendixB1NoiseTriplePMF_map_discreteTripleAtom]
  rw [PMF.map_comp]
  congr 1

theorem appendixB1GaussianMixtureRankingPMF_zero :
    appendixB1GaussianMixtureRankingPMF 0 = appendixB1RankingPMF := by
  have hmeasure :
      MeasurePreserving Prod.fst appendixB1GaussianLatentMeasure
        appendixB1NoiseTriplePMF.toMeasure := by
    unfold appendixB1GaussianLatentMeasure
    exact measurePreserving_fst
  have htransport :=
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      appendixB1GaussianLatentMeasure appendixB1NoiseTriplePMF.toMeasure
      Prod.fst hmeasure
      (appendixB1GaussianMixtureRank 0)
      (appendixB1GaussianMixtureRank_measurable 0)
      appendixB1DiscreteTripleRank appendixB1DiscreteTripleRank_measurable
      (by
        intro omega
        exact congrFun appendixB1GaussianMixtureRank_zero omega)
  change
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
      appendixB1GaussianLatentMeasure
      (appendixB1GaussianMixtureRank 0)
      (appendixB1GaussianMixtureRank_measurable 0) = _
  rw [htransport]
  rw [rankingPMFOfMeasure_from_finitePMF_eq_map
    appendixB1NoiseTriplePMF appendixB1DiscreteTripleRank
    appendixB1DiscreteTripleRank_measurable]
  exact appendixB1NoiseTriplePMF_map_discreteTripleRank

/-- Atomwise continuity of the actual B.1 Gaussian-mixture ranking law at zero scale. -/
theorem appendixB1GaussianMixtureRankingPMF_atom_continuousAt
    (pi : Ranking 1) :
    ContinuousAt
      (fun s => ((appendixB1GaussianMixtureRankingPMF s) pi).toReal) 0 := by
  apply AppliedModelingLib.continuousAt_of_epsilonContinuousAt
  change AppliedModelingLib.EpsilonContinuousAt
    (fun s =>
      ((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
        appendixB1GaussianLatentMeasure
        (appendixB1GaussianMixtureRank s)
        (appendixB1GaussianMixtureRank_measurable s)) pi).toReal) 0
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_atom_epsilonContinuousAt_of_ae_eventually_eq
      appendixB1GaussianLatentMeasure appendixB1GaussianMixtureRank
      appendixB1GaussianMixtureRank_measurable ?_ pi
  filter_upwards [] with omega
  let noise := appendixB1NoiseTripleFunction omega.1
  let perturb : ℝ → Candidate 1 → ℝ := fun s c =>
    s * appendixBGaussianTripleFunction omega.2 c
  have hstable :=
    appendixB1_rankByScore_eventually_eq_of_continuous_perturbation
      noise perturb
      (fun c => continuousAt_id.mul continuousAt_const)
      (fun c => by simp [perturb])
  have hzero : appendixB1GaussianMixtureScore 0 omega =
      appendixB1DiscreteScore (appendixB1NoiseTripleFunction omega.1) := by
    funext c
    simp [appendixB1GaussianMixtureScore]
  change ∀ᶠ θ in nhds 0,
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB1GaussianMixtureScore θ omega) =
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB1GaussianMixtureScore 0 omega)
  rw [hzero]
  simpa [appendixB1GaussianMixtureScore, noise, perturb] using hstable

/-- The B.1 source's strict reversal persists for a positive Gaussian component scale. -/
theorem appendixB1_gaussianMixture_reversal :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
          (appendixB1GaussianMixtureRankingPMF s)
          (appendixB1GaussianMixtureRankingPMF s) appendixB1Value -
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared
          (appendixB1GaussianMixtureRankingPMF s) appendixB1Value < 0 := by
  exact appendixB1_reversal_persists_of_atomwise_continuity
    appendixB1GaussianMixtureRankingPMF
    appendixB1GaussianMixtureRankingPMF_atom_continuousAt
    appendixB1GaussianMixtureRankingPMF_zero

/-! ## Appendix B.2 actual Gaussian mixtures -/

local instance : MeasurableSpace AppendixB2NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB2NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

abbrev AppendixB2NoiseTriple :=
  (AppendixB2NoiseAtom × AppendixB2NoiseAtom) × AppendixB2NoiseAtom

private theorem appendixB2NoiseWeight_nonneg_for_mixture
    (e : AppendixB2NoiseAtom) : 0 ≤ appendixB2NoiseWeight e := by
  cases e <;> norm_num [appendixB2NoiseWeight]

/-- The actual one-coordinate B.2 component-selection PMF. -/
noncomputable def appendixB2NoisePMF : PMF AppendixB2NoiseAtom :=
  AppliedModelingLib.finiteWeightedPMF
    appendixB2NoiseWeight appendixB2NoiseWeight_nonneg_for_mixture
    (by rw [appendixB2NoiseWeight_sum]; norm_num)

@[simp] theorem appendixB2NoisePMF_apply_toReal
    (e : AppendixB2NoiseAtom) :
    (appendixB2NoisePMF e).toReal = appendixB2NoiseWeight e := by
  rw [appendixB2NoisePMF,
    AppliedModelingLib.finiteWeightedPMF_apply_toReal]
  rw [appendixB2NoiseWeight_sum]
  simp

/-- Three independent B.2 component labels, one for each candidate. -/
noncomputable def appendixB2NoiseTriplePMF : PMF AppendixB2NoiseTriple :=
  AppliedModelingLib.pmfProd
    (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
    appendixB2NoisePMF

/-- The fixed latent probability space for B.2 Gaussian smoothing. -/
noncomputable def appendixB2GaussianLatentMeasure :
    Measure (AppendixB2NoiseTriple × AppendixBGaussianTriple) :=
  appendixB2NoiseTriplePMF.toMeasure.prod appendixBStandardGaussianTripleMeasure

instance : IsProbabilityMeasure appendixB2GaussianLatentMeasure := by
  unfold appendixB2GaussianLatentMeasure
  infer_instance

/-- Interpret the three finite B.2 component labels as a candidate-indexed draw. -/
def appendixB2NoiseTripleFunction
    (noise : AppendixB2NoiseTriple) : Candidate 1 → AppendixB2NoiseAtom
  | 0 => noise.1.1
  | 1 => noise.1.2
  | _ => noise.2

/-- B.2 algorithm scores with the source centers and Gaussian standard deviation `|s|`. -/
def appendixB2AlgorithmGaussianMixtureScore
    (s : ℝ) (omega : AppendixB2NoiseTriple × AppendixBGaussianTriple)
    (c : Candidate 1) : ℝ :=
  appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction omega.1) c +
    s * appendixBGaussianTripleFunction omega.2 c

/-- B.2 human scores with the source centers and Gaussian standard deviation `|s|`. -/
def appendixB2HumanGaussianMixtureScore
    (s : ℝ) (omega : AppendixB2NoiseTriple × AppendixBGaussianTriple)
    (c : Candidate 1) : ℝ :=
  appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction omega.1) c +
    s * appendixBGaussianTripleFunction omega.2 c

private theorem appendixB2GaussianMixturePerturbation_measurable
    (c : Candidate 1) :
    Measurable (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
      appendixBGaussianTripleFunction omega.2 c) := by
  fin_cases c <;> simp [appendixBGaussianTripleFunction]
  · exact measurable_fst.comp measurable_snd
  · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
  · exact measurable_snd.comp (measurable_snd.comp measurable_snd)

theorem appendixB2AlgorithmGaussianMixtureScore_measurable
    (s : ℝ) (c : Candidate 1) :
    Measurable (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
      appendixB2AlgorithmGaussianMixtureScore s omega c) := by
  unfold appendixB2AlgorithmGaussianMixtureScore
  have hcenter : Measurable
      (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
        appendixB2AlgorithmDiscreteScore
          (appendixB2NoiseTripleFunction omega.1) c) :=
    (measurable_of_finite
      (fun noise : AppendixB2NoiseTriple =>
        appendixB2AlgorithmDiscreteScore
          (appendixB2NoiseTripleFunction noise) c)).comp measurable_fst
  exact hcenter.add (measurable_const.mul
    (appendixB2GaussianMixturePerturbation_measurable c))

theorem appendixB2HumanGaussianMixtureScore_measurable
    (s : ℝ) (c : Candidate 1) :
    Measurable (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
      appendixB2HumanGaussianMixtureScore s omega c) := by
  unfold appendixB2HumanGaussianMixtureScore
  have hcenter : Measurable
      (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
        appendixB2HumanDiscreteScore
          (appendixB2NoiseTripleFunction omega.1) c) :=
    (measurable_of_finite
      (fun noise : AppendixB2NoiseTriple =>
        appendixB2HumanDiscreteScore
          (appendixB2NoiseTripleFunction noise) c)).comp measurable_fst
  exact hcenter.add (measurable_const.mul
    (appendixB2GaussianMixturePerturbation_measurable c))

/-- The ranking generated by the B.2 algorithmic Gaussian-mixture scores. -/
def appendixB2AlgorithmGaussianMixtureRank
    (s : ℝ) :
    (AppendixB2NoiseTriple × AppendixBGaussianTriple) → Ranking 1 :=
  fun omega =>
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (appendixB2AlgorithmGaussianMixtureScore s omega)

theorem appendixB2AlgorithmGaussianMixtureRank_measurable (s : ℝ) :
    Measurable (appendixB2AlgorithmGaussianMixtureRank s) := by
  unfold appendixB2AlgorithmGaussianMixtureRank
  exact AppliedModelingLib.SocialChoice.Ranking.measurable_rankByScore _
    (appendixB2AlgorithmGaussianMixtureScore_measurable s)

/-- The ranking generated by the B.2 human Gaussian-mixture scores. -/
def appendixB2HumanGaussianMixtureRank
    (s : ℝ) :
    (AppendixB2NoiseTriple × AppendixBGaussianTriple) → Ranking 1 :=
  fun omega =>
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (appendixB2HumanGaussianMixtureScore s omega)

theorem appendixB2HumanGaussianMixtureRank_measurable (s : ℝ) :
    Measurable (appendixB2HumanGaussianMixtureRank s) := by
  unfold appendixB2HumanGaussianMixtureRank
  exact AppliedModelingLib.SocialChoice.Ranking.measurable_rankByScore _
    (appendixB2HumanGaussianMixtureScore_measurable s)

/-- The actual B.2 algorithmic ranking PMF induced by the finite Gaussian mixture. -/
noncomputable def appendixB2AlgorithmGaussianMixtureRankingPMF (s : ℝ) :
    PMF (Ranking 1) :=
  rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
    (appendixB2AlgorithmGaussianMixtureRank s)
    (appendixB2AlgorithmGaussianMixtureRank_measurable s)

/-- The actual B.2 human ranking PMF induced by the finite Gaussian mixture. -/
noncomputable def appendixB2HumanGaussianMixtureRankingPMF (s : ℝ) :
    PMF (Ranking 1) :=
  rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
    (appendixB2HumanGaussianMixtureRank s)
    (appendixB2HumanGaussianMixtureRank_measurable s)

/-- The named Appendix-B ranking atom selected by an algorithmic B.2 component triple. -/
def appendixB2AlgorithmDiscreteTripleAtom
    (noise : AppendixB2NoiseTriple) : AppendixBRankingAtom :=
  appendixBRankingAtomOfScores
    (appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction noise) 0)
    (appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction noise) 1)
    (appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction noise) 2)

/-- The source's discrete B.2 algorithmic ranking map on the component triple. -/
def appendixB2AlgorithmDiscreteTripleRank
    (noise : AppendixB2NoiseTriple) : Ranking 1 :=
  (appendixB2AlgorithmDiscreteTripleAtom noise).toRanking

theorem appendixB2AlgorithmDiscreteTripleRank_measurable :
    Measurable appendixB2AlgorithmDiscreteTripleRank :=
  measurable_of_finite _

/-- The named Appendix-B ranking atom selected by a human B.2 component triple. -/
def appendixB2HumanDiscreteTripleAtom
    (noise : AppendixB2NoiseTriple) : AppendixBRankingAtom :=
  appendixBRankingAtomOfScores
    (appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction noise) 0)
    (appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction noise) 1)
    (appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction noise) 2)

/-- The source's discrete B.2 human ranking map on the component triple. -/
def appendixB2HumanDiscreteTripleRank
    (noise : AppendixB2NoiseTriple) : Ranking 1 :=
  (appendixB2HumanDiscreteTripleAtom noise).toRanking

theorem appendixB2HumanDiscreteTripleRank_measurable :
    Measurable appendixB2HumanDiscreteTripleRank :=
  measurable_of_finite _

theorem appendixB2_algorithm_rankByScore_discreteTriple_eq
    (noise : AppendixB2NoiseTriple) :
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction noise)) =
      appendixB2AlgorithmDiscreteTripleRank noise := by
  symm
  exact appendixBRankingAtom_rankByScore_eq_of_noTies
    (appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction noise))
    (appendixB2_algorithmDiscreteScore_noTies
      (appendixB2NoiseTripleFunction noise))

theorem appendixB2_human_rankByScore_discreteTriple_eq
    (noise : AppendixB2NoiseTriple) :
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction noise)) =
      appendixB2HumanDiscreteTripleRank noise := by
  symm
  exact appendixBRankingAtom_rankByScore_eq_of_noTies
    (appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction noise))
    (appendixB2_humanDiscreteScore_noTies
      (appendixB2NoiseTripleFunction noise))

theorem appendixB2AlgorithmGaussianMixtureRank_zero :
    appendixB2AlgorithmGaussianMixtureRank 0 =
      fun omega => appendixB2AlgorithmDiscreteTripleRank omega.1 := by
  funext omega
  unfold appendixB2AlgorithmGaussianMixtureRank
    appendixB2AlgorithmGaussianMixtureScore
  simpa using appendixB2_algorithm_rankByScore_discreteTriple_eq omega.1

theorem appendixB2HumanGaussianMixtureRank_zero :
    appendixB2HumanGaussianMixtureRank 0 =
      fun omega => appendixB2HumanDiscreteTripleRank omega.1 := by
  funext omega
  unfold appendixB2HumanGaussianMixtureRank appendixB2HumanGaussianMixtureScore
  simpa using appendixB2_human_rankByScore_discreteTriple_eq omega.1

@[simp] private theorem appendixB2NoiseTriplePMF_apply_toReal
    (e0 e1 e2 : AppendixB2NoiseAtom) :
    (appendixB2NoiseTriplePMF ((e0, e1), e2)).toReal =
      appendixB2NoiseWeight e0 * appendixB2NoiseWeight e1 *
        appendixB2NoiseWeight e2 := by
  rw [appendixB2NoiseTriplePMF,
    AppliedModelingLib.pmfProd_apply_toReal,
    AppliedModelingLib.pmfProd_apply_toReal]
  simp [mul_assoc]

/-- The finite component product pushes forward to the exact B.2 algorithmic atom table. -/
theorem appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleAtom :
    appendixB2NoiseTriplePMF.map appendixB2AlgorithmDiscreteTripleAtom =
      appendixB2AlgorithmAtomPMF := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff'
    ((appendixB2NoiseTriplePMF.map appendixB2AlgorithmDiscreteTripleAtom).apply_ne_top a)
    (appendixB2AlgorithmAtomPMF.apply_ne_top a)).mp
  rw [pmf_map_apply_toReal_fintype]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [appendixB2AlgorithmAtomPMF,
    AppliedModelingLib.finiteWeightedPMF_apply_toReal,
    appendixB2AlgorithmRankingWeight_sum]
  simp only [div_one]
  rw [appendixB2AlgorithmRankingWeight_eq_iid_rum_pushforward]
  simp [appendixB2AlgorithmIIDRUMRankingWeight,
    appendixB2AlgorithmDiscreteTripleAtom,
    appendixB2AlgorithmDiscreteScore, appendixB2NoiseTripleFunction,
    appendixB2Value, eq_comm]

/-- The finite component product pushes forward to the exact B.2 human atom table. -/
theorem appendixB2NoiseTriplePMF_map_humanDiscreteTripleAtom :
    appendixB2NoiseTriplePMF.map appendixB2HumanDiscreteTripleAtom =
      appendixB2HumanAtomPMF := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff'
    ((appendixB2NoiseTriplePMF.map appendixB2HumanDiscreteTripleAtom).apply_ne_top a)
    (appendixB2HumanAtomPMF.apply_ne_top a)).mp
  rw [pmf_map_apply_toReal_fintype]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [appendixB2HumanAtomPMF,
    AppliedModelingLib.finiteWeightedPMF_apply_toReal,
    appendixB2HumanRankingWeight_sum]
  simp only [div_one]
  rw [appendixB2HumanRankingWeight_eq_iid_rum_pushforward]
  simp [appendixB2HumanIIDRUMRankingWeight,
    appendixB2HumanDiscreteTripleAtom,
    appendixB2HumanDiscreteScore, appendixB2NoiseTripleFunction,
    appendixB2Value, eq_comm]

theorem appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleRank :
    appendixB2NoiseTriplePMF.map appendixB2AlgorithmDiscreteTripleRank =
      appendixB2AlgorithmRankingPMF := by
  unfold appendixB2AlgorithmRankingPMF
  rw [← appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleAtom]
  rw [PMF.map_comp]
  congr 1

theorem appendixB2NoiseTriplePMF_map_humanDiscreteTripleRank :
    appendixB2NoiseTriplePMF.map appendixB2HumanDiscreteTripleRank =
      appendixB2HumanRankingPMF := by
  unfold appendixB2HumanRankingPMF
  rw [← appendixB2NoiseTriplePMF_map_humanDiscreteTripleAtom]
  rw [PMF.map_comp]
  congr 1

theorem appendixB2AlgorithmGaussianMixtureRankingPMF_zero :
    appendixB2AlgorithmGaussianMixtureRankingPMF 0 =
      appendixB2AlgorithmRankingPMF := by
  have hmeasure :
      MeasurePreserving Prod.fst appendixB2GaussianLatentMeasure
        appendixB2NoiseTriplePMF.toMeasure := by
    unfold appendixB2GaussianLatentMeasure
    exact measurePreserving_fst
  have htransport :=
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      appendixB2GaussianLatentMeasure appendixB2NoiseTriplePMF.toMeasure
      Prod.fst hmeasure
      (appendixB2AlgorithmGaussianMixtureRank 0)
      (appendixB2AlgorithmGaussianMixtureRank_measurable 0)
      appendixB2AlgorithmDiscreteTripleRank
      appendixB2AlgorithmDiscreteTripleRank_measurable
      (by
        intro omega
        exact congrFun appendixB2AlgorithmGaussianMixtureRank_zero omega)
  change
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
      appendixB2GaussianLatentMeasure
      (appendixB2AlgorithmGaussianMixtureRank 0)
      (appendixB2AlgorithmGaussianMixtureRank_measurable 0) = _
  rw [htransport]
  rw [rankingPMFOfMeasure_from_finitePMF_eq_map
    appendixB2NoiseTriplePMF appendixB2AlgorithmDiscreteTripleRank
    appendixB2AlgorithmDiscreteTripleRank_measurable]
  exact appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleRank

theorem appendixB2HumanGaussianMixtureRankingPMF_zero :
    appendixB2HumanGaussianMixtureRankingPMF 0 = appendixB2HumanRankingPMF := by
  have hmeasure :
      MeasurePreserving Prod.fst appendixB2GaussianLatentMeasure
        appendixB2NoiseTriplePMF.toMeasure := by
    unfold appendixB2GaussianLatentMeasure
    exact measurePreserving_fst
  have htransport :=
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
      appendixB2GaussianLatentMeasure appendixB2NoiseTriplePMF.toMeasure
      Prod.fst hmeasure
      (appendixB2HumanGaussianMixtureRank 0)
      (appendixB2HumanGaussianMixtureRank_measurable 0)
      appendixB2HumanDiscreteTripleRank
      appendixB2HumanDiscreteTripleRank_measurable
      (by
        intro omega
        exact congrFun appendixB2HumanGaussianMixtureRank_zero omega)
  change
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
      appendixB2GaussianLatentMeasure
      (appendixB2HumanGaussianMixtureRank 0)
      (appendixB2HumanGaussianMixtureRank_measurable 0) = _
  rw [htransport]
  rw [rankingPMFOfMeasure_from_finitePMF_eq_map
    appendixB2NoiseTriplePMF appendixB2HumanDiscreteTripleRank
    appendixB2HumanDiscreteTripleRank_measurable]
  exact appendixB2NoiseTriplePMF_map_humanDiscreteTripleRank

/-- Atomwise continuity of the actual B.2 algorithmic Gaussian-mixture ranking law. -/
theorem appendixB2AlgorithmGaussianMixtureRankingPMF_atom_continuousAt
    (pi : Ranking 1) :
    ContinuousAt
      (fun s => ((appendixB2AlgorithmGaussianMixtureRankingPMF s) pi).toReal) 0 := by
  apply AppliedModelingLib.continuousAt_of_epsilonContinuousAt
  change AppliedModelingLib.EpsilonContinuousAt
    (fun s =>
      ((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
        appendixB2GaussianLatentMeasure
        (appendixB2AlgorithmGaussianMixtureRank s)
        (appendixB2AlgorithmGaussianMixtureRank_measurable s)) pi).toReal) 0
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_atom_epsilonContinuousAt_of_ae_eventually_eq
      appendixB2GaussianLatentMeasure appendixB2AlgorithmGaussianMixtureRank
      appendixB2AlgorithmGaussianMixtureRank_measurable ?_ pi
  filter_upwards [] with omega
  let noise := appendixB2NoiseTripleFunction omega.1
  let perturb : ℝ → Candidate 1 → ℝ := fun s c =>
    s * appendixBGaussianTripleFunction omega.2 c
  have hstable :=
    appendixB2_algorithmRankByScore_eventually_eq_of_continuous_perturbation
      noise perturb
      (fun c => continuousAt_id.mul continuousAt_const)
      (fun c => by simp [perturb])
  have hzero : appendixB2AlgorithmGaussianMixtureScore 0 omega =
      appendixB2AlgorithmDiscreteScore (appendixB2NoiseTripleFunction omega.1) := by
    funext c
    simp [appendixB2AlgorithmGaussianMixtureScore]
  change ∀ᶠ θ in nhds 0,
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB2AlgorithmGaussianMixtureScore θ omega) =
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB2AlgorithmGaussianMixtureScore 0 omega)
  rw [hzero]
  simpa [appendixB2AlgorithmGaussianMixtureScore, noise, perturb] using hstable

/-- Atomwise continuity of the actual B.2 human Gaussian-mixture ranking law. -/
theorem appendixB2HumanGaussianMixtureRankingPMF_atom_continuousAt
    (pi : Ranking 1) :
    ContinuousAt
      (fun s => ((appendixB2HumanGaussianMixtureRankingPMF s) pi).toReal) 0 := by
  apply AppliedModelingLib.continuousAt_of_epsilonContinuousAt
  change AppliedModelingLib.EpsilonContinuousAt
    (fun s =>
      ((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
        appendixB2GaussianLatentMeasure
        (appendixB2HumanGaussianMixtureRank s)
        (appendixB2HumanGaussianMixtureRank_measurable s)) pi).toReal) 0
  refine
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_atom_epsilonContinuousAt_of_ae_eventually_eq
      appendixB2GaussianLatentMeasure appendixB2HumanGaussianMixtureRank
      appendixB2HumanGaussianMixtureRank_measurable ?_ pi
  filter_upwards [] with omega
  let noise := appendixB2NoiseTripleFunction omega.1
  let perturb : ℝ → Candidate 1 → ℝ := fun s c =>
    s * appendixBGaussianTripleFunction omega.2 c
  have hstable :=
    appendixB2_humanRankByScore_eventually_eq_of_continuous_perturbation
      noise perturb
      (fun c => continuousAt_id.mul continuousAt_const)
      (fun c => by simp [perturb])
  have hzero : appendixB2HumanGaussianMixtureScore 0 omega =
      appendixB2HumanDiscreteScore (appendixB2NoiseTripleFunction omega.1) := by
    funext c
    simp [appendixB2HumanGaussianMixtureScore]
  change ∀ᶠ θ in nhds 0,
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB2HumanGaussianMixtureScore θ omega) =
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (appendixB2HumanGaussianMixtureScore 0 omega)
  rw [hzero]
  simpa [appendixB2HumanGaussianMixtureScore, noise, perturb] using hstable

/-- The B.2 source's strict reversal persists for a positive Gaussian component scale. -/
theorem appendixB2_gaussianMixture_reversal :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      0 <
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            (appendixB2HumanGaussianMixtureRankingPMF s)
            (appendixB2AlgorithmGaussianMixtureRankingPMF s) appendixB2Value -
          AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            (appendixB2HumanGaussianMixtureRankingPMF s)
            (appendixB2HumanGaussianMixtureRankingPMF s) appendixB2Value := by
  exact appendixB2_reversal_persists_of_atomwise_continuity
    appendixB2AlgorithmGaussianMixtureRankingPMF
    appendixB2HumanGaussianMixtureRankingPMF
    appendixB2AlgorithmGaussianMixtureRankingPMF_atom_continuousAt
    appendixB2HumanGaussianMixtureRankingPMF_atom_continuousAt
    appendixB2AlgorithmGaussianMixtureRankingPMF_zero
    appendixB2HumanGaussianMixtureRankingPMF_zero

end

end KR21Monoculture

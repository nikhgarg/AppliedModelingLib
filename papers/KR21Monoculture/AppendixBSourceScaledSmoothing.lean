import KR21Monoculture.AppendixBGaussianMixture

/-!
# Appendix B source-scaled Gaussian smoothing

The Appendix B.2 comparison is between two accuracy values of *one* RUM
family.  Thus its Gaussian component noise is sampled once from a fixed base
law and is then divided by the relevant accuracy parameter.  In particular,
at `theta_A = 11 / 10` and `theta_H = 9 / 10`, a base component standard
deviation `s` becomes `(10 / 11) * s` and `(10 / 9) * s`, respectively.

This file records that common-noise semantic bridge and transfers the existing
finite-rank continuity proof to the source-correct pair.  It deliberately does
not claim the remaining analytic fact that this finite Gaussian-mixture family
satisfies every clause of Definition 1; that requires a separate bridge from
its explicit density to the corrected global-`W^{1,1}` source theorem.
-/

open AppliedModelingLib
open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace KR21Monoculture

noncomputable section

/-! The finite B.2 component carrier is discrete in this independent module. -/

local instance : MeasurableSpace AppendixB2NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB2NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-! ## One fixed base-noise RUM family -/

/--
The single-coordinate base noise for the B.2 smooth source model: first draw a
finite source atom, then add a Gaussian perturbation with standard deviation
`|s|`.  The same function is used for every accuracy value below.
-/
def appendixB2SourceGaussianMixtureNoise
    (s : ℝ) (omega : AppendixB2NoiseTriple × AppendixBGaussianTriple)
    (c : Candidate 1) : ℝ :=
  appendixB2NoiseValue (appendixB2NoiseTripleFunction omega.1 c) +
    s * appendixBGaussianTripleFunction omega.2 c

theorem appendixB2SourceGaussianMixtureNoise_measurable
    (s : ℝ) (c : Candidate 1) :
    Measurable (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
      appendixB2SourceGaussianMixtureNoise s omega c) := by
  unfold appendixB2SourceGaussianMixtureNoise
  have hcenter : Measurable
      (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
        appendixB2NoiseValue (appendixB2NoiseTripleFunction omega.1 c)) :=
    (measurable_of_finite
      (fun noise : AppendixB2NoiseTriple =>
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))).comp
      measurable_fst
  have hperturb : Measurable
      (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
        appendixBGaussianTripleFunction omega.2 c) := by
    fin_cases c <;> simp [appendixBGaussianTripleFunction]
    · exact measurable_fst.comp measurable_snd
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact hcenter.add (measurable_const.mul hperturb)

/-- The ranking induced by the fixed B.2 base noise at accuracy `theta`. -/
def appendixB2SourceGaussianMixtureRank
    (s theta : ℝ) :
    (AppendixB2NoiseTriple × AppendixBGaussianTriple) → Ranking 1 :=
  fun omega =>
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (fun c => appendixB2Value c +
        appendixB2SourceGaussianMixtureNoise s omega c / theta)

theorem appendixB2SourceGaussianMixtureRank_measurable
    (s theta : ℝ) :
    Measurable (appendixB2SourceGaussianMixtureRank s theta) := by
  unfold appendixB2SourceGaussianMixtureRank
  exact AppliedModelingLib.SocialChoice.Ranking.measurable_rankByScore _
    (fun c => measurable_const.add
      ((appendixB2SourceGaussianMixtureNoise_measurable s c).div_const theta))

/--
The actual B.2 source family with one fixed iid finite Gaussian-mixture noise
law.  Its width is `s`; `theta` is solely the paper's accuracy parameter.
-/
noncomputable def appendixB2SourceGaussianMixtureFamily
    (s : ℝ) : AccuracyFamily 1 where
  dist := fun theta =>
    rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
      (appendixB2SourceGaussianMixtureRank s theta)
      (appendixB2SourceGaussianMixtureRank_measurable s theta)
  value := appendixB2Value

/-! ## Identification at the two source accuracies -/

/--
At `theta_A = 11 / 10`, the fixed source noise is divided by `theta_A`.
Consequently both its component centers and its Gaussian standard deviation are
multiplied by `10 / 11`.
-/
theorem appendixB2SourceGaussianMixtureFamily_dist_thetaA
    (s : ℝ) :
    (appendixB2SourceGaussianMixtureFamily s).dist (11 / 10) =
      appendixB2AlgorithmGaussianMixtureRankingPMF ((10 / 11) * s) := by
  change
    rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
      (appendixB2SourceGaussianMixtureRank s (11 / 10))
      (appendixB2SourceGaussianMixtureRank_measurable s (11 / 10)) =
      appendixB2AlgorithmGaussianMixtureRankingPMF ((10 / 11) * s)
  unfold appendixB2AlgorithmGaussianMixtureRankingPMF
  congr 1
  funext omega
  unfold appendixB2SourceGaussianMixtureRank
    appendixB2AlgorithmGaussianMixtureRank
  congr 1
  funext c
  unfold appendixB2SourceGaussianMixtureNoise
    appendixB2AlgorithmGaussianMixtureScore
    appendixB2AlgorithmDiscreteScore
  ring

/--
At `theta_H = 9 / 10`, the same fixed source noise is divided by `theta_H`.
Consequently both its component centers and its Gaussian standard deviation are
multiplied by `10 / 9`.
-/
theorem appendixB2SourceGaussianMixtureFamily_dist_thetaH
    (s : ℝ) :
    (appendixB2SourceGaussianMixtureFamily s).dist (9 / 10) =
      appendixB2HumanGaussianMixtureRankingPMF ((10 / 9) * s) := by
  change
    rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
      (appendixB2SourceGaussianMixtureRank s (9 / 10))
      (appendixB2SourceGaussianMixtureRank_measurable s (9 / 10)) =
      appendixB2HumanGaussianMixtureRankingPMF ((10 / 9) * s)
  unfold appendixB2HumanGaussianMixtureRankingPMF
  congr 1
  funext omega
  unfold appendixB2SourceGaussianMixtureRank
    appendixB2HumanGaussianMixtureRank
  congr 1
  funext c
  unfold appendixB2SourceGaussianMixtureNoise
    appendixB2HumanGaussianMixtureScore
    appendixB2HumanDiscreteScore
  ring

/-! ## Correctly coupled smoothing endpoint -/

theorem appendixB2SourceGaussianMixtureFamily_thetaA_atom_continuousAt
    (pi : Ranking 1) :
    ContinuousAt
      (fun s =>
        (((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10)) pi).toReal)
      0 := by
  have hscale : ContinuousAt (fun s : ℝ => (10 / 11 : ℝ) * s) (0 : ℝ) :=
    continuousAt_const.mul continuousAt_id
  simpa only [appendixB2SourceGaussianMixtureFamily_dist_thetaA] using
    (appendixB2AlgorithmGaussianMixtureRankingPMF_atom_continuousAt pi).comp_of_eq
      hscale (by norm_num)

theorem appendixB2SourceGaussianMixtureFamily_thetaH_atom_continuousAt
    (pi : Ranking 1) :
    ContinuousAt
      (fun s =>
        (((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10)) pi).toReal)
      0 := by
  have hscale : ContinuousAt (fun s : ℝ => (10 / 9 : ℝ) * s) (0 : ℝ) :=
    continuousAt_const.mul continuousAt_id
  simpa only [appendixB2SourceGaussianMixtureFamily_dist_thetaH] using
    (appendixB2HumanGaussianMixtureRankingPMF_atom_continuousAt pi).comp_of_eq
      hscale (by norm_num)

/--
The source-correct B.2 smoothing conclusion.  For every sufficiently small
positive component width, the two laws are `F_{11/10}` and `F_{9/10}` of one
fixed iid Gaussian-mixture source, and the literal Appendix-B payoff reversal
remains strict.
-/
theorem appendixB2_sourceScaledGaussianMixture_reversal :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      0 <
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            ((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
            appendixB2Value -
          AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            appendixB2Value := by
  exact appendixB2_reversal_persists_of_atomwise_continuity
    (fun s => (appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
    (fun s => (appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
    appendixB2SourceGaussianMixtureFamily_thetaA_atom_continuousAt
    appendixB2SourceGaussianMixtureFamily_thetaH_atom_continuousAt
    (by
      change (appendixB2SourceGaussianMixtureFamily (0 : ℝ)).dist (11 / 10) = _
      rw [appendixB2SourceGaussianMixtureFamily_dist_thetaA]
      simpa only [mul_zero] using appendixB2AlgorithmGaussianMixtureRankingPMF_zero)
    (by
      change (appendixB2SourceGaussianMixtureFamily (0 : ℝ)).dist (9 / 10) = _
      rw [appendixB2SourceGaussianMixtureFamily_dist_thetaH]
      simpa only [mul_zero] using appendixB2HumanGaussianMixtureRankingPMF_zero)

end

end KR21Monoculture

import KR21Monoculture.GumbelPlackettLuceExact
import KR21Monoculture.PlackettLuceOuterSource
import KR21Monoculture.PlackettLuceStrategyDominance
import KR21Monoculture.W11ScoreTransport

/-!
# Positive-scale Gumbel RUM transport

This module formalizes the literal random-utility construction with iid
innovations `-s * log T`, where `T` has unit-rate exponential law and
`s > 0`.  Its induced ranking law is the independently constructed
Plackett--Luce law at inverse temperature `theta / s`.

The result is deliberately scale-parametric.  In particular, the repository's
named `unitVarianceGumbelScale` is not used here: no variance calculation and
no identification with the source's printed unit-variance normalization is
asserted or needed for this scale-invariant conclusion.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

noncomputable section

/-- A literal scale-`s` Gumbel innovation generated from a unit-rate
exponential arrival. -/
noncomputable def positiveScaleGumbelInnovation (s arrival : ℝ) : ℝ :=
  -s * Real.log arrival

/-- The scalar law of the literal scale-`s` Gumbel innovation. -/
noncomputable def positiveScaleGumbelMeasure (s : ℝ) : Measure ℝ :=
  (expMeasure 1).map (positiveScaleGumbelInnovation s)

/-- The iid scale-`s` Gumbel innovation vector obtained from exponential
arrivals. -/
noncomputable def positiveScaleGumbelNoise {n : ℕ} (s : ℝ)
    (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => positiveScaleGumbelInnovation s (arrival i)

/-- The source-style random-utility scores `value + (-s log T) / theta`. -/
noncomputable def positiveScaleGumbelScores {n : ℕ}
    (s theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => value i + positiveScaleGumbelNoise s arrival i / theta

/-- The total ranking map induced by the literal positive-scale Gumbel RUM. -/
noncomputable def positiveScaleGumbelRank {n : ℕ}
    (s theta : ℝ) (value : Candidate n → ℝ) :
    (Candidate n → ℝ) → Ranking n :=
  fun arrival => rankByScore (positiveScaleGumbelScores s theta value arrival)

theorem positiveScaleGumbelInnovation_eq_scaleOne (s arrival : ℝ) :
    positiveScaleGumbelInnovation s arrival =
      s * scaleOneGumbelInnovation arrival := by
  unfold positiveScaleGumbelInnovation scaleOneGumbelInnovation
  ring

theorem measurable_positiveScaleGumbelInnovation (s : ℝ) :
    Measurable (positiveScaleGumbelInnovation s) := by
  unfold positiveScaleGumbelInnovation
  exact measurable_const.mul Real.measurable_log

theorem positiveScaleGumbelMeasure_isProbabilityMeasure (s : ℝ) :
    IsProbabilityMeasure (positiveScaleGumbelMeasure s) := by
  unfold positiveScaleGumbelMeasure
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.isProbabilityMeasure_map
    (measurable_positiveScaleGumbelInnovation s).aemeasurable

/-- Coordinatewise transformation of the actual iid exponential arrival law
is exactly the iid product law of literal scale-`s` Gumbel innovations. -/
theorem positiveScaleGumbelNoise_law {n : ℕ} (s : ℝ) :
    Measure.map (positiveScaleGumbelNoise s) (gumbelArrivalLaw n) =
      Measure.pi (fun _ : Candidate n => positiveScaleGumbelMeasure s) := by
  have hsourceProbability :
      ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) :=
    hsourceProbability
  letI : ∀ _ : Candidate n,
      IsProbabilityMeasure (positiveScaleGumbelMeasure s) := fun _ =>
    positiveScaleGumbelMeasure_isProbabilityMeasure s
  let hcoordinate : ∀ i : Candidate n,
      MeasurePreserving (positiveScaleGumbelInnovation s)
        (expMeasure 1) (positiveScaleGumbelMeasure s) := fun _ =>
    ⟨measurable_positiveScaleGumbelInnovation s, rfl⟩
  have hpi := measurePreserving_pi
    (fun _ : Candidate n => expMeasure 1)
    (fun _ : Candidate n => positiveScaleGumbelMeasure s)
    hcoordinate
  change Measure.map (fun arrival : Candidate n → ℝ =>
      fun i => positiveScaleGumbelInnovation s (arrival i))
      (Measure.pi (fun _ : Candidate n => expMeasure 1)) = _
  simpa only [positiveScaleGumbelNoise] using hpi.map_eq

theorem measurable_positiveScaleGumbelScores {n : ℕ}
    (s theta : ℝ) (value : Candidate n → ℝ) :
    ∀ i : Candidate n,
      Measurable fun arrival : Candidate n → ℝ =>
        positiveScaleGumbelScores s theta value arrival i := by
  intro i
  unfold positiveScaleGumbelScores positiveScaleGumbelNoise
  exact measurable_const.add
    (((measurable_positiveScaleGumbelInnovation s).comp (measurable_pi_apply i)).div
      measurable_const)

theorem measurable_positiveScaleGumbelRank {n : ℕ}
    (s theta : ℝ) (value : Candidate n → ℝ) :
    Measurable (positiveScaleGumbelRank s theta value) := by
  unfold positiveScaleGumbelRank
  exact measurable_rankByScore _
    (measurable_positiveScaleGumbelScores s theta value)

/-- The actual finite ranking PMF of the iid literal scale-`s` Gumbel RUM. -/
noncomputable def positiveScaleGumbelRUMRankingPMF {n : ℕ}
    (s theta : ℝ) (value : Candidate n → ℝ) : PMF (Ranking n) := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  exact rankingPMFOfMeasure (gumbelArrivalLaw n)
    (positiveScaleGumbelRank s theta value)
    (measurable_positiveScaleGumbelRank s theta value)

/-- At positive scale and positive accuracy, multiplying the literal
source-style scores by `theta / s` gives the scale-one additive score vector.
The equality therefore preserves the canonical ranking including tie-breaking.
-/
theorem positiveScaleGumbelRank_eq_scaleOneGumbelRank {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) (arrival : Candidate n → ℝ) :
    positiveScaleGumbelRank s theta value arrival =
      scaleOneGumbelRank (theta / s) value arrival := by
  have htemperature : 0 < theta / s := div_pos htheta hs
  have hscores :
      (fun i : Candidate n =>
        (theta / s) * positiveScaleGumbelScores s theta value arrival i) =
        scaleOneGumbelScores (theta / s) value arrival := by
    funext i
    unfold positiveScaleGumbelScores positiveScaleGumbelNoise
      positiveScaleGumbelInnovation scaleOneGumbelScores scaleOneGumbelNoise
      scaleOneGumbelInnovation
    field_simp [ne_of_gt hs, ne_of_gt htheta]
  unfold positiveScaleGumbelRank scaleOneGumbelRank
  rw [← hscores]
  exact (rankByScore_pos_scale
    (positiveScaleGumbelScores s theta value arrival) htemperature).symm

/-- The literal iid scale-`s` Gumbel RUM has the same ranking PMF as the
actual scale-one Gumbel construction at inverse temperature `theta / s`. -/
theorem positiveScaleGumbelRUMRankingPMF_eq_scaleOne {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    positiveScaleGumbelRUMRankingPMF s theta value =
      scaleOneGumbelRUMRankingPMF (theta / s) value := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  apply rankingPMFOfMeasure_eq_of_measurePreserving
    (gumbelArrivalLaw n) (gumbelArrivalLaw n) id
    (MeasurePreserving.id (gumbelArrivalLaw n))
    (positiveScaleGumbelRank s theta value)
    (measurable_positiveScaleGumbelRank s theta value)
    (scaleOneGumbelRank (theta / s) value)
    (measurable_scaleOneGumbelRank _ _)
  intro arrival
  simpa using
    positiveScaleGumbelRank_eq_scaleOneGumbelRank hs htheta value arrival

/-- Exact scale-parametric Gumbel/Plackett--Luce law.  The inverse temperature
is visibly `theta / s`; this theorem has no variance-normalization premise. -/
theorem positiveScaleGumbelRUMRankingPMF_eq_plackettLuce {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    positiveScaleGumbelRUMRankingPMF s theta value =
      plackettLuceRankingPMF (theta / s) value := by
  rw [positiveScaleGumbelRUMRankingPMF_eq_scaleOne hs htheta value]
  exact scaleOneGumbelRUMRankingPMF_eq_plackettLuce _ _

/-- Adding one common scalar to all scores preserves the canonical ranking,
including deterministic tie-breaking. -/
theorem rankByScore_add_common
    {n : ℕ} (score : Candidate n → ℝ) (location : ℝ) :
    rankByScore (fun i => score i + location) = rankByScore score := by
  classical
  let pi : Ranking n := rankByScore score
  have hpi : pi = Tuple.sort (fun i : Candidate n => -score i) := by
    rfl
  have hsorted :
      Monotone ((fun i : Candidate n => -score i) ∘ pi) := by
    simpa [pi] using Tuple.monotone_sort (fun i : Candidate n => -score i)
  have htied :
      ∀ i j : Candidate n, i < j →
        ((fun c : Candidate n => -score c) ∘ pi) i =
            ((fun c : Candidate n => -score c) ∘ pi) j →
          pi i < pi j := by
    intro i j hij heq
    exact
      (Tuple.eq_sort_iff (f := fun c : Candidate n => -score c) (σ := pi)).mp hpi |>.2
        i j hij heq
  have hshift :
      ∀ i : Candidate n, -(score i + location) = -score i - location := by
    intro i
    ring
  have hpi_shifted : pi = Tuple.sort (fun i : Candidate n => -(score i + location)) := by
    apply (Tuple.eq_sort_iff (f := fun i : Candidate n => -(score i + location))
      (σ := pi)).mpr
    constructor
    · intro i j hij
      rw [Function.comp_apply, Function.comp_apply, hshift, hshift]
      exact sub_le_sub_right (hsorted hij) location
    · intro i j hij heq
      apply htied i j hij
      change -score (pi i) = -score (pi j)
      rw [hshift (pi i), hshift (pi j)] at heq
      exact sub_left_inj.mp heq
  simpa [pi, rankByScore] using hpi_shifted.symm

/-- A literal location-`location`, scale-`s` Gumbel innovation, obtained
from a unit-rate exponential arrival. -/
noncomputable def commonLocationPositiveScaleGumbelInnovation
    (location s arrival : ℝ) : ℝ :=
  location + positiveScaleGumbelInnovation s arrival

/-- The scalar law of the literal common-location, positive-scale Gumbel innovation. -/
noncomputable def commonLocationPositiveScaleGumbelMeasure
    (location s : ℝ) : Measure ℝ :=
  (expMeasure 1).map (commonLocationPositiveScaleGumbelInnovation location s)

/-- The iid common-location, positive-scale Gumbel innovation vector. -/
noncomputable def commonLocationPositiveScaleGumbelNoise {n : ℕ}
    (location s : ℝ) (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => commonLocationPositiveScaleGumbelInnovation location s (arrival i)

/-- Source-style random-utility scores with a common innovation location. -/
noncomputable def commonLocationPositiveScaleGumbelScores {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => value i + commonLocationPositiveScaleGumbelNoise location s arrival i / theta

/-- Total canonical ranking induced by the common-location Gumbel scores. -/
noncomputable def commonLocationPositiveScaleGumbelRank {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ) :
    (Candidate n → ℝ) → Ranking n :=
  fun arrival => rankByScore
    (commonLocationPositiveScaleGumbelScores location s theta value arrival)

theorem measurable_commonLocationPositiveScaleGumbelInnovation
    (location s : ℝ) :
    Measurable (commonLocationPositiveScaleGumbelInnovation location s) := by
  unfold commonLocationPositiveScaleGumbelInnovation
  exact measurable_const.add (measurable_positiveScaleGumbelInnovation s)

theorem commonLocationPositiveScaleGumbelMeasure_isProbabilityMeasure
    (location s : ℝ) :
    IsProbabilityMeasure (commonLocationPositiveScaleGumbelMeasure location s) := by
  unfold commonLocationPositiveScaleGumbelMeasure
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.isProbabilityMeasure_map
    (measurable_commonLocationPositiveScaleGumbelInnovation location s).aemeasurable

/-- Coordinatewise transformation of the iid exponential source is exactly
the iid product law of the common-location Gumbel innovations. -/
theorem commonLocationPositiveScaleGumbelNoise_law {n : ℕ}
    (location s : ℝ) :
    Measure.map (commonLocationPositiveScaleGumbelNoise location s) (gumbelArrivalLaw n) =
      Measure.pi (fun _ : Candidate n =>
        commonLocationPositiveScaleGumbelMeasure location s) := by
  have hsourceProbability :
      ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) :=
    hsourceProbability
  letI : ∀ _ : Candidate n,
      IsProbabilityMeasure (commonLocationPositiveScaleGumbelMeasure location s) := fun _ =>
    commonLocationPositiveScaleGumbelMeasure_isProbabilityMeasure location s
  let hcoordinate : ∀ i : Candidate n,
      MeasurePreserving (commonLocationPositiveScaleGumbelInnovation location s)
        (expMeasure 1) (commonLocationPositiveScaleGumbelMeasure location s) := fun _ =>
    ⟨measurable_commonLocationPositiveScaleGumbelInnovation location s, rfl⟩
  have hpi := measurePreserving_pi
    (fun _ : Candidate n => expMeasure 1)
    (fun _ : Candidate n => commonLocationPositiveScaleGumbelMeasure location s)
    hcoordinate
  change Measure.map (fun arrival : Candidate n → ℝ =>
      fun i => commonLocationPositiveScaleGumbelInnovation location s (arrival i))
      (Measure.pi (fun _ : Candidate n => expMeasure 1)) = _
  simpa only [commonLocationPositiveScaleGumbelNoise] using hpi.map_eq

theorem commonLocationPositiveScaleGumbelScores_eq_add_common {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) :
    commonLocationPositiveScaleGumbelScores location s theta value arrival =
      fun i => positiveScaleGumbelScores s theta value arrival i + location / theta := by
  funext i
  unfold commonLocationPositiveScaleGumbelScores
    commonLocationPositiveScaleGumbelNoise
    commonLocationPositiveScaleGumbelInnovation
    positiveScaleGumbelScores positiveScaleGumbelNoise
  rw [add_div]
  ring

/-- A common location shift has no effect on the total score ranking,
including any exact ties. -/
theorem commonLocationPositiveScaleGumbelRank_eq_positiveScaleGumbelRank {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) :
    commonLocationPositiveScaleGumbelRank location s theta value arrival =
      positiveScaleGumbelRank s theta value arrival := by
  unfold commonLocationPositiveScaleGumbelRank positiveScaleGumbelRank
  rw [commonLocationPositiveScaleGumbelScores_eq_add_common]
  exact rankByScore_add_common _ _

theorem measurable_commonLocationPositiveScaleGumbelRank {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ) :
    Measurable (commonLocationPositiveScaleGumbelRank location s theta value) := by
  have hrank :
      commonLocationPositiveScaleGumbelRank location s theta value =
        positiveScaleGumbelRank s theta value := by
    funext arrival
    exact commonLocationPositiveScaleGumbelRank_eq_positiveScaleGumbelRank
      location s theta value arrival
  rw [hrank]
  exact measurable_positiveScaleGumbelRank s theta value

/-- The actual finite ranking PMF of the common-location, positive-scale
Gumbel RUM. -/
noncomputable def commonLocationPositiveScaleGumbelRUMRankingPMF {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ) : PMF (Ranking n) := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  exact rankingPMFOfMeasure (gumbelArrivalLaw n)
    (commonLocationPositiveScaleGumbelRank location s theta value)
    (measurable_commonLocationPositiveScaleGumbelRank location s theta value)

theorem commonLocationPositiveScaleGumbelRUMRankingPMF_eq_positiveScale {n : ℕ}
    (location s theta : ℝ) (value : Candidate n → ℝ) :
    commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value =
      positiveScaleGumbelRUMRankingPMF s theta value := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  apply rankingPMFOfMeasure_eq_of_measurePreserving
    (gumbelArrivalLaw n) (gumbelArrivalLaw n) id
    (MeasurePreserving.id (gumbelArrivalLaw n))
    (commonLocationPositiveScaleGumbelRank location s theta value)
    (measurable_commonLocationPositiveScaleGumbelRank location s theta value)
    (positiveScaleGumbelRank s theta value)
    (measurable_positiveScaleGumbelRank s theta value)
  intro arrival
  simpa using commonLocationPositiveScaleGumbelRank_eq_positiveScaleGumbelRank
    location s theta value arrival

/-- Exact common-location, positive-scale Gumbel/Plackett--Luce bridge. -/
theorem commonLocationPositiveScaleGumbelRUMRankingPMF_eq_plackettLuce {n : ℕ}
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value =
      plackettLuceRankingPMF (theta / s) value := by
  rw [commonLocationPositiveScaleGumbelRUMRankingPMF_eq_positiveScale]
  exact positiveScaleGumbelRUMRankingPMF_eq_plackettLuce hs htheta value

end

namespace DistributionalAccuracyFamily

/-- The profile-indexed family induced by one fixed, explicitly positive-scale
Gumbel innovation law.  Positivity of `s` is required only by the theorems
that compare this family to a positive inverse temperature. -/
noncomputable def positiveScaleGumbelRUMDistributionalFamily {n : ℕ}
    (s : ℝ) : DistributionalAccuracyFamily n where
  dist := fun theta value => positiveScaleGumbelRUMRankingPMF s theta value

@[simp] theorem positiveScaleGumbelRUMDistributionalFamily_dist {n : ℕ}
    (s theta : ℝ) (value : ValueProfile n) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value =
      positiveScaleGumbelRUMRankingPMF s theta value := rfl

/-- The literal positive-scale RUM law is the sequential Plackett--Luce law
at the visibly corrected inverse temperature `theta / s`. -/
theorem positiveScaleGumbelRUM_pointwise_eq_plackettLuce {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : ValueProfile n) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value =
      plackettLuceRankingPMF (theta / s) value := by
  exact positiveScaleGumbelRUMRankingPMF_eq_plackettLuce hs htheta value

/-- Atomwise measurability of the actual positive-scale RUM kernel follows
from its proved pointwise equality to the independently defined sequential
Plackett--Luce PMF. -/
theorem positiveScaleGumbelRUM_ranking_atom_measurable {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (ranking : Ranking n) :
    Measurable fun value : ValueProfile n =>
      (positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value ranking := by
  have heq :
      (fun value : ValueProfile n =>
        (positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value ranking) =
        fun value => plackettLuceRankingPMF (theta / s) value ranking := by
    funext value
    rw [positiveScaleGumbelRUM_pointwise_eq_plackettLuce hs htheta]
  rw [heq]
  exact plackettLuce_ranking_atom_measurable (theta / s) ranking

/-- The profilewise conditionally independent ranking-pair PMFs agree under
the literal positive-scale Gumbel/Plackett--Luce bridge. -/
theorem positiveScaleGumbelRUM_independentPairLaw_eq_plackettLuce {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : ValueProfile n) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).independentPairLaw theta value =
      (plackettLuceDistributionalFamily (n := n)).independentPairLaw
        (theta / s) value := by
  unfold independentPairLaw
  rw [positiveScaleGumbelRUM_pointwise_eq_plackettLuce hs htheta]
  rfl

/-- The two conditional ranking-pair kernels are equal, including the actual
measure representation used by the outer experiment. -/
theorem positiveScaleGumbelRUM_independentPairKernel_eq_plackettLuce {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).independentPairKernel theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) =
      (plackettLuceDistributionalFamily (n := n)).independentPairKernel
        (theta / s)
        (fun ranking => plackettLuce_ranking_atom_measurable (theta / s) ranking) := by
  apply Kernel.ext
  intro value
  rw [independentPairKernel_apply, independentPairKernel_apply]
  rw [positiveScaleGumbelRUM_independentPairLaw_eq_plackettLuce hs htheta]

/-- The actual outer profile/ranking-pair measures agree.  This transports
the source's conditional event at the measure level, not merely atomwise. -/
theorem positiveScaleGumbelRUM_outerIndependentPairJointLaw_eq_plackettLuce
    {n : ℕ} (D : Measure (ValueProfile n)) {s theta : ℝ}
    (hs : 0 < s) (htheta : 0 < theta) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerIndependentPairJointLaw D theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) =
      (plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D
        (theta / s)
        (fun ranking => plackettLuce_ranking_atom_measurable (theta / s) ranking) := by
  unfold outerIndependentPairJointLaw
  rw [positiveScaleGumbelRUM_independentPairKernel_eq_plackettLuce hs htheta]

/-- At every realized profile, the independent-minus-shared reranking effect
of the literal positive-scale Gumbel RUM is zero. -/
theorem positiveScaleGumbelRUM_pointwise_rerankingGain_eq_zero {n : ℕ}
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : ValueProfile n) :
    expectedRerankingGain
      ((positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value)
      value = 0 := by
  rw [positiveScaleGumbelRUM_pointwise_eq_plackettLuce hs htheta]
  exact plackettLuce_pointwise_rerankingGain_eq_zero (theta / s) value

/-- The outer-D restricted gain numerator is zero for every outer measure.
This is a direct semantic consequence of the proved pointwise RUM law. -/
theorem positiveScaleGumbelRUM_outerDisagreementGainNumerator_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) {s theta : ℝ}
    (hs : 0 < s) (htheta : 0 < theta) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerDisagreementGainNumerator
      D theta = 0 := by
  rw [outerDisagreementGainNumerator_eq_outerExpected]
  unfold outerExpected
  change ∫ value : ValueProfile n,
      expectedRerankingGain
        ((positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value)
        value ∂D = 0
  have hzero :
      (fun value : ValueProfile n =>
        expectedRerankingGain
          ((positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value)
          value) = fun _ => 0 := by
    funext value
    exact positiveScaleGumbelRUM_pointwise_rerankingGain_eq_zero hs htheta value
  rw [hzero, integral_zero]

/-- The outer-D conditional reranking gain is zero, with the standard
zero-mass convention made explicit by the underlying definition. -/
theorem positiveScaleGumbelRUM_outerDisagreementConditionalGain_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) {s theta : ℝ}
    (hs : 0 < s) (htheta : 0 < theta) :
    (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerDisagreementConditionalGain
      D theta = 0 := by
  unfold outerDisagreementConditionalGain
  rw [positiveScaleGumbelRUM_outerDisagreementGainNumerator_eq_zero D hs htheta]
  simp

/-- With a probability outer profile law, the literal positive-scale Gumbel
profile/ranking-pair measure is a genuine probability law. -/
theorem positiveScaleGumbelRUM_outerJointLaw_isProbability {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta) :
    IsProbabilityMeasure
      ((positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerIndependentPairJointLaw D theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking)) := by
  exact (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerIndependentPairJointLaw_isProbability
    D theta (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking)

/-- The full outer experiment has positive top-disagreement probability for
the literal positive-scale Gumbel RUM. -/
theorem positiveScaleGumbelRUM_outerJointDisagreementEvent_pos {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerIndependentPairJointLaw D theta
          (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) := by
  rw [positiveScaleGumbelRUM_outerIndependentPairJointLaw_eq_plackettLuce D hs htheta]
  exact plackettLuce_outerJointDisagreementEvent_pos D (theta / s)

/-- Under finite coordinatewise first moments, the literal conditional gain
in the actual positive-scale Gumbel outer experiment is zero. -/
theorem positiveScaleGumbelRUM_jointLawDisagreementConditionalGain_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    jointLawDisagreementConditionalGain
      (positiveScaleGumbelRUMDistributionalFamily (n := n) s) D theta
      (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) = 0 := by
  calc
    jointLawDisagreementConditionalGain
        (positiveScaleGumbelRUMDistributionalFamily (n := n) s) D theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) =
      jointLawDisagreementConditionalGain
        (plackettLuceDistributionalFamily (n := n)) D (theta / s)
        (fun ranking => plackettLuce_ranking_atom_measurable (theta / s) ranking) := by
        unfold jointLawDisagreementConditionalGain
        rw [positiveScaleGumbelRUM_outerIndependentPairJointLaw_eq_plackettLuce D hs htheta]
    _ = 0 := plackettLuce_jointLawDisagreementConditionalGain_eq_zero D
      (theta / s) hvalue

/-- Complete source-style outer-D endpoint for the literal positive-scale
Gumbel construction: the top-disagreement event has positive mass and its
actual conditional gain is zero. -/
theorem positiveScaleGumbelRUM_source_jointConditionalGain_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerIndependentPairJointLaw D theta
          (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking)) ∧
      jointLawDisagreementConditionalGain
        (positiveScaleGumbelRUMDistributionalFamily (n := n) s) D theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) = 0 := by
  exact ⟨positiveScaleGumbelRUM_outerJointDisagreementEvent_pos D hs htheta,
    positiveScaleGumbelRUM_jointLawDisagreementConditionalGain_eq_zero D hs htheta hvalue⟩

/-- The profile-indexed family induced by literal iid Gumbel innovations with
one common location and one positive scale.  The location is intentionally an
arbitrary real: it is transported semantically rather than normalized away. -/
noncomputable def commonLocationPositiveScaleGumbelRUMDistributionalFamily {n : ℕ}
    (location s : ℝ) : DistributionalAccuracyFamily n where
  dist := fun theta value =>
    commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value

@[simp] theorem commonLocationPositiveScaleGumbelRUMDistributionalFamily_dist {n : ℕ}
    (location s theta : ℝ) (value : ValueProfile n) :
    (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).dist
        theta value =
      commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value := rfl

/-- A common innovation location leaves the profilewise ranking PMF equal to
the corresponding zero-location positive-scale family. -/
theorem commonLocationPositiveScaleGumbelRUM_pointwise_eq_positiveScale {n : ℕ}
    (location s theta : ℝ) (value : ValueProfile n) :
    (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).dist
        theta value =
      (positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value := by
  exact commonLocationPositiveScaleGumbelRUMRankingPMF_eq_positiveScale
    location s theta value

/-- Atomwise measurability of the common-location family follows from its
proved equality to the zero-location family, not from a location convention. -/
theorem commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable {n : ℕ}
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (ranking : Ranking n) :
    Measurable fun value : ValueProfile n =>
      (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).dist
        theta value ranking := by
  have heq :
      (fun value : ValueProfile n =>
        (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).dist
          theta value ranking) =
        fun value =>
          (positiveScaleGumbelRUMDistributionalFamily (n := n) s).dist theta value ranking := by
    funext value
    rw [commonLocationPositiveScaleGumbelRUM_pointwise_eq_positiveScale]
  rw [heq]
  exact positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking

/-- The profilewise independent ranking-pair laws are equal under a common
innovation location. -/
theorem commonLocationPositiveScaleGumbelRUM_independentPairLaw_eq_positiveScale {n : ℕ}
    (location s theta : ℝ) (value : ValueProfile n) :
    (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).independentPairLaw
        theta value =
      (positiveScaleGumbelRUMDistributionalFamily (n := n) s).independentPairLaw theta value := by
  unfold independentPairLaw
  rw [commonLocationPositiveScaleGumbelRUM_pointwise_eq_positiveScale]

/-- Equality of the actual conditional ranking-pair kernels under a common
location shift. -/
theorem commonLocationPositiveScaleGumbelRUM_independentPairKernel_eq_positiveScale {n : ℕ}
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta) :
    (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).independentPairKernel
        theta (fun ranking =>
          commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) =
      (positiveScaleGumbelRUMDistributionalFamily (n := n) s).independentPairKernel theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) := by
  apply Kernel.ext
  intro value
  rw [independentPairKernel_apply, independentPairKernel_apply]
  rw [commonLocationPositiveScaleGumbelRUM_independentPairLaw_eq_positiveScale]

/-- The full outer profile/ranking-pair measures agree under a common Gumbel
location shift. -/
theorem commonLocationPositiveScaleGumbelRUM_outerIndependentPairJointLaw_eq_positiveScale
    {n : ℕ} (D : Measure (ValueProfile n)) {location s theta : ℝ}
    (hs : 0 < s) (htheta : 0 < theta) :
    (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).outerIndependentPairJointLaw D theta
          (fun ranking =>
            commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) =
      (positiveScaleGumbelRUMDistributionalFamily (n := n) s).outerIndependentPairJointLaw D theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) := by
  unfold outerIndependentPairJointLaw
  rw [commonLocationPositiveScaleGumbelRUM_independentPairKernel_eq_positiveScale hs htheta]

/-- The common-location outer experiment has positive top-disagreement mass
whenever the outer profile law is a probability law. -/
theorem commonLocationPositiveScaleGumbelRUM_outerJointDisagreementEvent_pos {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).outerIndependentPairJointLaw D theta
            (fun ranking =>
              commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) := by
  rw [commonLocationPositiveScaleGumbelRUM_outerIndependentPairJointLaw_eq_positiveScale
    D hs htheta]
  exact positiveScaleGumbelRUM_outerJointDisagreementEvent_pos D hs htheta

/-- Under coordinatewise first moments, the actual common-location outer
conditional gain is zero. -/
theorem commonLocationPositiveScaleGumbelRUM_jointLawDisagreementConditionalGain_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    jointLawDisagreementConditionalGain
      (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s) D theta
      (fun ranking =>
        commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) = 0 := by
  calc
    jointLawDisagreementConditionalGain
        (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s) D theta
        (fun ranking =>
          commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) =
      jointLawDisagreementConditionalGain
        (positiveScaleGumbelRUMDistributionalFamily (n := n) s) D theta
        (fun ranking => positiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) := by
        unfold jointLawDisagreementConditionalGain
        rw [commonLocationPositiveScaleGumbelRUM_outerIndependentPairJointLaw_eq_positiveScale
          D hs htheta]
    _ = 0 := positiveScaleGumbelRUM_jointLawDisagreementConditionalGain_eq_zero D
      hs htheta hvalue

/-- Complete source-facing outer-D endpoint for iid Gumbel innovations with
an arbitrary common location and positive common scale. -/
theorem commonLocationPositiveScaleGumbelRUM_source_jointConditionalGain_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s).outerIndependentPairJointLaw D theta
            (fun ranking =>
              commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking)) ∧
      jointLawDisagreementConditionalGain
        (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n) location s) D theta
        (fun ranking =>
          commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable hs htheta ranking) = 0 := by
  exact ⟨commonLocationPositiveScaleGumbelRUM_outerJointDisagreementEvent_pos D hs htheta,
    commonLocationPositiveScaleGumbelRUM_jointLawDisagreementConditionalGain_eq_zero D hs htheta hvalue⟩

end DistributionalAccuracyFamily

/-- Semantic Section-3.1 best-available conclusion for one fixed positive
Gumbel scale.  The comparison is made from the two actual ranking PMFs and
their payoff consequences; it does not infer quality from an agent label or
from a variance-normalization convention. -/
theorem positiveScaleGumbel_best_available_weakly_dominates {n : ℕ}
    {s thetaA thetaH : ℝ} (hs : 0 < s)
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking := positiveScaleGumbelRUMRankingPMF s thetaA value
        humanRanking := positiveScaleGumbelRUMRankingPMF s thetaH value
        value := value }
    (thetaH ≤ thetaA →
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
          Model.payoffAgainst M Strategy.human Strategy.human) ∧
      (thetaA ≤ thetaH →
        Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
          Model.payoffAgainst M Strategy.human Strategy.human ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.human) := by
  rw [positiveScaleGumbelRUMRankingPMF_eq_plackettLuce hs hthetaA value,
    positiveScaleGumbelRUMRankingPMF_eq_plackettLuce hs hthetaH value]
  have hpl := plackettLuce_best_available_weakly_dominates value
    (div_pos hthetaA hs) (div_pos hthetaH hs)
  constructor
  · intro htheta
    exact hpl.1 (div_le_div_of_nonneg_right htheta hs.le)
  · intro htheta
    exact hpl.2 (div_le_div_of_nonneg_right htheta hs.le)

/-- Semantic Section-3.1 weak-best-available conclusion for two iid Gumbel
RUMs sharing an arbitrary common location and a fixed positive scale. -/
theorem commonLocationPositiveScaleGumbel_best_available_weakly_dominates {n : ℕ}
    {location s thetaA thetaH : ℝ} (hs : 0 < s)
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking :=
          commonLocationPositiveScaleGumbelRUMRankingPMF location s thetaA value
        humanRanking :=
          commonLocationPositiveScaleGumbelRUMRankingPMF location s thetaH value
        value := value }
    (thetaH ≤ thetaA →
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
          Model.payoffAgainst M Strategy.human Strategy.human) ∧
      (thetaA ≤ thetaH →
        Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
          Model.payoffAgainst M Strategy.human Strategy.human ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.human) := by
  rw [commonLocationPositiveScaleGumbelRUMRankingPMF_eq_positiveScale,
    commonLocationPositiveScaleGumbelRUMRankingPMF_eq_positiveScale]
  exact positiveScaleGumbel_best_available_weakly_dominates hs value hthetaA hthetaH

end KR21Monoculture

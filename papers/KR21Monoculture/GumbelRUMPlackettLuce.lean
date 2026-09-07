import KR21Monoculture.PlackettLuce
import AppliedModelingLib.Foundations.Probability.Exponential
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Independence.Basic

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-!
# Gumbel random utilities and the Plackett--Luce bridge

Section 3.1 of KR21 invokes the classical Gumbel/Plackett--Luce equivalence.
This file keeps the two sides separate.  The Gumbel side is an actual
probability law: a scale-one Gumbel innovation is `-log T` for a unit-rate
exponential `T`, and the finite candidate vector is an iid product measure.
The Plackett--Luce side remains the independently constructed finite PMF in
`PlackettLuce.lean`.

The remaining analytic bridge is explicitly exposed below as probabilities of
strict exponential-race cells.  In particular, no definition here identifies a
Gumbel law with the sequential PMF by fiat.
-/

/-- A scale-one standard Gumbel innovation, represented as `-log T` for a
unit-rate exponential arrival time `T`. -/
noncomputable def scaleOneGumbelInnovation (arrival : ℝ) : ℝ :=
  -Real.log arrival

/-- The actual scalar source measure for a scale-one Gumbel innovation. -/
noncomputable def scaleOneGumbelMeasure : Measure ℝ :=
  (expMeasure 1).map scaleOneGumbelInnovation

/-- Independent unit-rate exponential arrivals, one for every finite candidate. -/
noncomputable def gumbelArrivalLaw (n : ℕ) : Measure (Candidate n → ℝ) :=
  Measure.pi (fun _ : Candidate n => expMeasure 1)

/-- The scale-one Gumbel noise vector obtained coordinatewise from arrivals. -/
noncomputable def scaleOneGumbelNoise {n : ℕ}
    (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => scaleOneGumbelInnovation (arrival i)

/-- Additive scores in the scale-one Gumbel RUM. -/
noncomputable def scaleOneGumbelScores {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => theta * value i + scaleOneGumbelNoise arrival i

/-- The total score-ranking map for the actual Gumbel source model.

`rankByScore` has deterministic tie-breaking.  The later strict-race
certificate records the separate null-tie proof needed to replace those total
ranking events with strict exponential-race cells.
-/
noncomputable def scaleOneGumbelRank {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    (Candidate n → ℝ) → Ranking n :=
  fun arrival => rankByScore (scaleOneGumbelScores theta value arrival)

theorem measurable_scaleOneGumbelInnovation :
    Measurable scaleOneGumbelInnovation := by
  unfold scaleOneGumbelInnovation
  exact Real.measurable_log.neg

theorem measurable_scaleOneGumbelScores {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    ∀ i : Candidate n,
      Measurable fun arrival : Candidate n → ℝ =>
        scaleOneGumbelScores theta value arrival i := by
  intro i
  unfold scaleOneGumbelScores scaleOneGumbelNoise
  exact measurable_const.add
    (measurable_scaleOneGumbelInnovation.comp (measurable_pi_apply i))

theorem measurable_scaleOneGumbelRank {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    Measurable (scaleOneGumbelRank theta value) := by
  unfold scaleOneGumbelRank
  exact measurable_rankByScore _ (measurable_scaleOneGumbelScores theta value)

/-- The unit-rate exponential arrival law is a genuine finite iid probability law. -/
theorem gumbelArrivalLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gumbelArrivalLaw n) := by
  letI : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  unfold gumbelArrivalLaw
  infer_instance

/-- Every coordinate of the actual iid exponential source vector is positive
almost surely.  This discharges the domain condition for the logarithmic
Gumbel transform without treating `log` as total on the support by convention.
-/
theorem gumbelArrivalLaw_ae_positive {n : ℕ} :
    ∀ᵐ arrival ∂gumbelArrivalLaw n, ∀ i : Candidate n, 0 < arrival i := by
  have hprob : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  let M : AppliedModelingLib.Probability.Exponential.Model := ⟨1, by norm_num⟩
  have hbase_zero : expMeasure 1 (Set.Iic (0 : ℝ)) = 0 := by
    simpa [M, AppliedModelingLib.Probability.Exponential.Model.measure] using
      M.measure_Iic_zero
  have hbase : ∀ᵐ x ∂expMeasure 1, 0 < x := by
    exact (measure_eq_zero_iff_ae_notMem.1 hbase_zero).mono fun x hx =>
      lt_of_not_ge hx
  have hcoordinate : ∀ i : Candidate n,
      ∀ᵐ arrival ∂gumbelArrivalLaw n, 0 < arrival i := by
    intro i
    have hpres : MeasurePreserving (Function.eval i)
        (gumbelArrivalLaw n) (expMeasure 1) := by
      simpa [gumbelArrivalLaw] using
        (@measurePreserving_eval
          (Candidate n) (fun _ : Candidate n => ℝ) inferInstance
          (fun _ => inferInstance)
          (fun _ : Candidate n => expMeasure 1) hprob i)
    exact hpres.quasiMeasurePreserving.tendsto_ae hbase
  simpa only [Filter.eventually_all] using hcoordinate

/-- The transformed scalar Gumbel source law is a probability law. -/
theorem scaleOneGumbelMeasure_isProbabilityMeasure :
    IsProbabilityMeasure scaleOneGumbelMeasure := by
  unfold scaleOneGumbelMeasure
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.isProbabilityMeasure_map measurable_scaleOneGumbelInnovation.aemeasurable

/-- The actual finite ranking PMF of iid scale-one Gumbel random utilities. -/
noncomputable def scaleOneGumbelRUMRankingPMF {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) : PMF (Ranking n) := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  exact rankingPMFOfMeasure (gumbelArrivalLaw n)
    (scaleOneGumbelRank theta value)
    (measurable_scaleOneGumbelRank theta value)

/-- The scale selected for the repository's explicit scaled-`-log Exp(1)`
convention.  Proving its variance and identifying it with the paper's
unit-variance Gumbel source law is a separate source-model obligation. -/
noncomputable def unitVarianceGumbelScale : ℝ := Real.sqrt 6 / Real.pi

theorem unitVarianceGumbelScale_pos : 0 < unitVarianceGumbelScale := by
  unfold unitVarianceGumbelScale
  exact div_pos (Real.sqrt_pos.2 (by norm_num)) Real.pi_pos

/-- The repository's explicit scaled Gumbel score convention:
`value i + (sqrt 6 / pi) * G_i / theta`. -/
noncomputable def unitVarianceGumbelScores {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) : Candidate n → ℝ :=
  fun i => value i + unitVarianceGumbelScale * scaleOneGumbelNoise arrival i / theta

/-- The repository's scaled Gumbel rank map, totalized by the library's
deterministic tie convention. -/
noncomputable def unitVarianceGumbelRank {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    (Candidate n → ℝ) → Ranking n :=
  fun arrival => rankByScore (unitVarianceGumbelScores theta value arrival)

theorem measurable_unitVarianceGumbelRank {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    Measurable (unitVarianceGumbelRank theta value) := by
  unfold unitVarianceGumbelRank
  apply measurable_rankByScore
  intro i
  unfold unitVarianceGumbelScores scaleOneGumbelNoise
  exact measurable_const.add
    ((measurable_const.mul
      (measurable_scaleOneGumbelInnovation.comp (measurable_pi_apply i))).div
        measurable_const)

/-- The ranking PMF induced by the repository's explicit scaled Gumbel
convention. -/
noncomputable def unitVarianceGumbelRUMRankingPMF {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) : PMF (Ranking n) := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  exact rankingPMFOfMeasure (gumbelArrivalLaw n)
    (unitVarianceGumbelRank theta value)
    (measurable_unitVarianceGumbelRank theta value)

/-- Positive rescaling preserves the canonical `rankByScore` ranking,
including its deterministic tie-breaking. -/
private theorem rankByScore_pos_scale
    {n : ℕ} (score : Candidate n → ℝ) {scale : ℝ} (hscale : 0 < scale) :
    rankByScore (fun i => scale * score i) = rankByScore score := by
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
  have hscale_neg :
      ∀ i : Candidate n, -(scale * score i) = scale * (-score i) := by
    intro i
    ring
  have hpi_scaled : pi = Tuple.sort (fun i : Candidate n => -(scale * score i)) := by
    apply (Tuple.eq_sort_iff (f := fun i : Candidate n => -(scale * score i))
      (σ := pi)).mpr
    constructor
    · intro i j hij
      rw [Function.comp_apply, Function.comp_apply, hscale_neg, hscale_neg]
      exact mul_le_mul_of_nonneg_left (hsorted hij) hscale.le
    · intro i j hij heq
      apply htied i j hij
      change -score (pi i) = -score (pi j)
      rw [hscale_neg (pi i), hscale_neg (pi j)] at heq
      exact mul_left_cancel₀ (ne_of_gt hscale) heq
  simpa [pi, rankByScore] using hpi_scaled.symm

/-- At positive accuracy, the explicit scaled Gumbel score convention is
exactly the scale-one Gumbel score convention at inverse temperature
`theta / (sqrt 6 / pi)`, after multiplying all scores by a positive scalar. -/
theorem unitVarianceGumbelRank_eq_scaleOneGumbelRank {n : ℕ}
    {theta : ℝ} (htheta : 0 < theta) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) :
    unitVarianceGumbelRank theta value arrival =
      scaleOneGumbelRank (theta / unitVarianceGumbelScale) value arrival := by
  let scale : ℝ := theta / unitVarianceGumbelScale
  have hscale : 0 < scale := div_pos htheta unitVarianceGumbelScale_pos
  have hscores :
      (fun i : Candidate n => scale * unitVarianceGumbelScores theta value arrival i) =
        scaleOneGumbelScores scale value arrival := by
    funext i
    unfold scale unitVarianceGumbelScores scaleOneGumbelScores
      scaleOneGumbelNoise
    field_simp [ne_of_gt htheta, ne_of_gt unitVarianceGumbelScale_pos]
  unfold unitVarianceGumbelRank scaleOneGumbelRank
  rw [← hscores]
  exact (rankByScore_pos_scale (unitVarianceGumbelScores theta value arrival) hscale).symm

/-- The repository's explicit scaled Gumbel RUM has the same finite ranking
law as the scale-one construction at inverse temperature `theta / (sqrt 6 /
pi)`.  This is an equality of measure-induced PMFs, not a definition of
either law. -/
theorem unitVarianceGumbelRUMRankingPMF_eq_scaleOne {n : ℕ}
    {theta : ℝ} (htheta : 0 < theta) (value : Candidate n → ℝ) :
    unitVarianceGumbelRUMRankingPMF theta value =
      scaleOneGumbelRUMRankingPMF
        (theta / unitVarianceGumbelScale) value := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  apply rankingPMFOfMeasure_eq_of_measurePreserving
    (gumbelArrivalLaw n) (gumbelArrivalLaw n) id
    (MeasurePreserving.id (gumbelArrivalLaw n))
    (unitVarianceGumbelRank theta value)
    (measurable_unitVarianceGumbelRank theta value)
    (scaleOneGumbelRank (theta / unitVarianceGumbelScale) value)
    (measurable_scaleOneGumbelRank _ _)
  intro arrival
  simpa using unitVarianceGumbelRank_eq_scaleOneGumbelRank htheta value arrival

/-- Exponential race times corresponding to the scale-one Gumbel scores.
Their rates are exactly the source equation-(7) weights `exp(theta * value i)`.
-/
noncomputable def gumbelRaceTime {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) (i : Candidate n) : ℝ :=
  Real.exp (-theta * value i) * arrival i

/-- The full vector of transformed exponential race times. -/
noncomputable def gumbelRaceVector {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    (Candidate n → ℝ) → Candidate n → ℝ :=
  fun arrival i => gumbelRaceTime theta value arrival i

theorem measurable_gumbelRaceVector {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    Measurable (gumbelRaceVector theta value) := by
  unfold gumbelRaceVector gumbelRaceTime
  exact measurable_pi_lambda _ fun _ =>
    measurable_const.mul (measurable_pi_apply _)

/-- A positive scalar rescaling of a unit-rate exponential variable has the
inverse rescaled rate.  This is kept as a measure equality so later race
arguments cannot silently replace the transformed Gumbel arrivals by a
different law. -/
private theorem map_unitExp_mul_eq_expMeasure_inv
    {scale : ℝ} (hscale : 0 < scale) :
    Measure.map (fun x : ℝ => scale * x) (expMeasure 1) =
      expMeasure scale⁻¹ := by
  let unitModel : AppliedModelingLib.Probability.Exponential.Model := ⟨1, by norm_num⟩
  let scaledModel : AppliedModelingLib.Probability.Exponential.Model :=
    ⟨scale⁻¹, inv_pos.mpr hscale⟩
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (expMeasure scale⁻¹) :=
    isProbabilityMeasure_expMeasure (inv_pos.mpr hscale)
  apply ext_of_generate_finite (Set.range Set.Ioi)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ))
    isPiSystem_Ioi
  · rintro _ ⟨threshold, rfl⟩
    rw [Measure.map_apply (μ := expMeasure 1) (f := fun x : ℝ => scale * x)
      (measurable_const.mul measurable_id) measurableSet_Ioi]
    rw [Set.preimage_const_mul_Ioi₀ threshold hscale]
    by_cases hthreshold : 0 ≤ threshold
    · apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top _ _) (measure_ne_top _ _)).mp
      rw [show (expMeasure 1) = unitModel.measure by rfl,
        show (expMeasure scale⁻¹) = scaledModel.measure by rfl,
        unitModel.measure_Ioi_toReal
          (div_nonneg hthreshold hscale.le),
        scaledModel.measure_Ioi_toReal hthreshold]
      congr 1
      dsimp [unitModel, scaledModel]
      field_simp [ne_of_gt hscale]
    · have hneg : threshold < 0 := lt_of_not_ge hthreshold
      have hdivneg : threshold / scale < 0 := div_neg_of_neg_of_pos hneg hscale
      have hunit_zero : (expMeasure 1) (Set.Iic (threshold / scale)) = 0 := by
        let M : AppliedModelingLib.Probability.Exponential.Model := ⟨1, by norm_num⟩
        apply measure_mono_null ?_ M.measure_Iio_zero
        intro x hx
        exact lt_of_le_of_lt hx hdivneg
      have hscaled_zero : (expMeasure scale⁻¹) (Set.Iic threshold) = 0 := by
        let M : AppliedModelingLib.Probability.Exponential.Model :=
          ⟨scale⁻¹, inv_pos.mpr hscale⟩
        apply measure_mono_null ?_ M.measure_Iio_zero
        intro x hx
        exact lt_of_le_of_lt hx hneg
      rw [show Set.Ioi (threshold / scale) = (Set.Iic (threshold / scale))ᶜ by
          ext x; simp,
        show Set.Ioi threshold = (Set.Iic threshold)ᶜ by ext x; simp,
        measure_compl measurableSet_Iic (measure_ne_top _ _), hunit_zero,
        measure_compl measurableSet_Iic (measure_ne_top _ _), hscaled_zero,
        measure_univ, measure_univ]
  · rw [Measure.map_apply (μ := expMeasure 1) (f := fun x : ℝ => scale * x)
      (measurable_const.mul measurable_id) MeasurableSet.univ]
    simp

/-- The rate of the transformed Gumbel race time is exactly the corresponding
Plackett--Luce weight. -/
private theorem gumbelRaceTime_scalar_law {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (i : Candidate n) :
    (expMeasure 1).map (fun x : ℝ => Real.exp (-theta * value i) * x) =
      expMeasure (plackettLuceWeight theta value i) := by
  rw [map_unitExp_mul_eq_expMeasure_inv (Real.exp_pos _)]
  unfold plackettLuceWeight
  congr 1
  rw [show -theta * value i = -(theta * value i) by ring,
    Real.exp_neg, inv_inv]

/-- The whole transformed Gumbel vector has the actual independent
heterogeneous exponential product law whose rates are the Plackett--Luce
weights.  The remaining open race theorem therefore has no Gumbel semantics
left to assume: it is the finite strict-order formula for this displayed
product measure. -/
theorem gumbelRaceVector_law {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    Measure.map (gumbelRaceVector theta value) (gumbelArrivalLaw n) =
      Measure.pi (fun i : Candidate n =>
        expMeasure (plackettLuceWeight theta value i)) := by
  have hprob : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  have hscalar : ∀ i : Candidate n,
      Measure.map (fun x : ℝ => Real.exp (-theta * value i) * x) (expMeasure 1) =
        expMeasure (plackettLuceWeight theta value i) := by
    intro i
    exact gumbelRaceTime_scalar_law theta value i
  let hpres : ∀ i : Candidate n,
      MeasurePreserving (fun x : ℝ => Real.exp (-theta * value i) * x)
        (expMeasure 1) (expMeasure (plackettLuceWeight theta value i)) := fun i =>
    ⟨measurable_const.mul measurable_id, hscalar i⟩
  letI : ∀ i : Candidate n,
      IsProbabilityMeasure (expMeasure (plackettLuceWeight theta value i)) := fun i =>
    isProbabilityMeasure_expMeasure (plackettLuceWeight_pos theta value i)
  have hpi := measurePreserving_pi
    (fun _ : Candidate n => expMeasure 1)
    (fun i : Candidate n => expMeasure (plackettLuceWeight theta value i)) hpres
  change Measure.map (fun arrival : Candidate n → ℝ =>
      fun i => Real.exp (-theta * value i) * arrival i)
      (Measure.pi (fun _ : Candidate n => expMeasure 1)) = _
  simpa only [neg_mul] using hpi.map_eq

/-- The strict Gumbel race has no equality between any two distinct candidate
times.  It is stated separately because the total `rankByScore` construction
has a deterministic tie convention even before this null-event fact is proved.
-/
def GumbelRaceNoTies {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) : Prop :=
  ∀ᵐ arrival ∂gumbelArrivalLaw n,
    ∀ i j : Candidate n, i ≠ j →
      gumbelRaceTime theta value arrival i ≠
        gumbelRaceTime theta value arrival j

theorem gumbelRaceTime_pos {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) (i : Candidate n)
    (harrival : 0 < arrival i) :
    0 < gumbelRaceTime theta value arrival i := by
  unfold gumbelRaceTime
  exact mul_pos (Real.exp_pos _) harrival

/-- On the actual positive exponential support, an additive scale-one Gumbel
score is exactly the negative logarithm of its transformed race time. -/
theorem scaleOneGumbelScore_eq_neg_log_raceTime {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) (i : Candidate n)
    (harrival : 0 < arrival i) :
    scaleOneGumbelScores theta value arrival i =
      -Real.log (gumbelRaceTime theta value arrival i) := by
  unfold scaleOneGumbelScores scaleOneGumbelNoise scaleOneGumbelInnovation
    gumbelRaceTime
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt harrival), Real.log_exp]
  ring

/-- On positive arrivals, score order is the reverse of exponential-race time
order.  This is the deterministic Gumbel-to-race geometry used by the missing
probabilistic cell calculation. -/
theorem scaleOneGumbelScore_lt_iff_raceTime_gt {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) (i j : Candidate n)
    (hi : 0 < arrival i) (hj : 0 < arrival j) :
    scaleOneGumbelScores theta value arrival i <
        scaleOneGumbelScores theta value arrival j ↔
      gumbelRaceTime theta value arrival j <
        gumbelRaceTime theta value arrival i := by
  rw [scaleOneGumbelScore_eq_neg_log_raceTime theta value arrival i hi,
    scaleOneGumbelScore_eq_neg_log_raceTime theta value arrival j hj,
    neg_lt_neg_iff]
  exact Real.log_lt_log_iff
    (gumbelRaceTime_pos theta value arrival j hj)
    (gumbelRaceTime_pos theta value arrival i hi)

/-- For a tie-free score vector, a proposed ranking is its canonical score
ranking exactly when scores strictly decrease along that ranking. -/
private theorem rankByScore_eq_iff_strict_ranking_order_of_noTies {n : ℕ}
    (score : Candidate n → ℝ) (ranking : Ranking n)
    (hnoTies : ∀ i j : Candidate n, i ≠ j → score i ≠ score j) :
    rankByScore score = ranking ↔
      ∀ p q : Candidate n, p < q → score (ranking q) < score (ranking p) := by
  constructor
  · intro hrank p q hpq
    have hweak : score (ranking q) ≤ score (ranking p) := by
      apply rankByScore_weaklyOrdersScores score
      rw [hrank]
      simpa [rankOf] using hpq.le
    refine lt_of_le_of_ne hweak ?_
    apply hnoTies (ranking q) (ranking p)
    intro hcandidate
    have hposition : q = p := ranking.injective hcandidate
    exact (ne_of_lt hpq) hposition.symm
  · intro hstrict
    classical
    let pi : Ranking n := ranking
    have hsort : pi = Tuple.sort (fun c : Candidate n => -score c) := by
      refine (Tuple.eq_sort_iff
        (f := fun c : Candidate n => -score c) (σ := pi)).mpr ?_
      constructor
      · intro p q hpq
        rcases lt_or_eq_of_le hpq with hpq' | rfl
        · have h := hstrict p q hpq'
          dsimp [Function.comp_def]
          linarith
        · rfl
      · intro p q hpq heq
        exfalso
        have h := hstrict p q hpq
        change -score (pi p) = -score (pi q) at heq
        linarith
    simpa [pi, rankByScore] using hsort.symm

private theorem scaledExponentialMeasure_noAtoms {scale : ℝ} (hscale : 0 < scale) :
    NoAtoms ((expMeasure 1).map fun x : ℝ => scale * x) := by
  letI : NoAtoms (expMeasure 1) := by
    unfold expMeasure gammaMeasure
    infer_instance
  refine ⟨?_⟩
  intro y
  have hmeasurable : Measurable (fun x : ℝ => scale * x) :=
    measurable_const.mul measurable_id
  rw [Measure.map_apply hmeasurable (measurableSet_singleton y)]
  have hpreimage :
      (fun x : ℝ => scale * x) ⁻¹' ({y} : Set ℝ) = {y / scale} := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact (eq_div_iff (ne_of_gt hscale)).2 (by simpa [mul_comm] using h)
    · intro h
      exact (by simpa [mul_comm] using (eq_div_iff (ne_of_gt hscale)).1 h)
  rw [hpreimage]
  exact measure_singleton _

private theorem prod_real_diagonal_measure_zero
    (mu nu : Measure ℝ) [SFinite mu] [SFinite nu] [NoAtoms nu] :
    (mu.prod nu) {pair : ℝ × ℝ | pair.1 = pair.2} = 0 := by
  let diagonal : Set (ℝ × ℝ) := {pair | pair.1 = pair.2}
  have hdiagonal_measurable : MeasurableSet diagonal :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hsection : ∀ x : ℝ, nu (Prod.mk x ⁻¹' diagonal) = 0 := by
    intro x
    have hpreimage : Prod.mk x ⁻¹' diagonal = ({x} : Set ℝ) := by
      ext y
      simp [diagonal]
    rw [hpreimage]
    exact measure_singleton _
  calc
    (mu.prod nu) {pair : ℝ × ℝ | pair.1 = pair.2} =
        (mu.prod nu) diagonal := rfl
    _ = ∫⁻ x, nu (Prod.mk x ⁻¹' diagonal) ∂mu := by
      rw [Measure.prod_apply hdiagonal_measurable]
    _ = ∫⁻ _x, 0 ∂mu := by
      exact lintegral_congr hsection
    _ = 0 := by simp

private theorem gumbelRaceCoordinate_measurable {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (i : Candidate n) :
    Measurable fun arrival : Candidate n → ℝ =>
      gumbelRaceTime theta value arrival i := by
  unfold gumbelRaceTime
  exact measurable_const.mul (measurable_pi_apply i)

private theorem gumbelRaceCoordinate_map_eq_scaledExponential {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (i : Candidate n) :
    Measure.map (fun arrival : Candidate n → ℝ =>
      gumbelRaceTime theta value arrival i) (gumbelArrivalLaw n) =
      (expMeasure 1).map (fun x : ℝ => Real.exp (-theta * value i) * x) := by
  have hprob : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  have hpres : MeasurePreserving (Function.eval i)
      (gumbelArrivalLaw n) (expMeasure 1) := by
    simpa [gumbelArrivalLaw] using
      (@measurePreserving_eval
        (Candidate n) (fun _ : Candidate n => ℝ) inferInstance
        (fun _ => inferInstance)
        (fun _ : Candidate n => expMeasure 1) hprob i)
  calc
    Measure.map (fun arrival : Candidate n → ℝ =>
        gumbelRaceTime theta value arrival i) (gumbelArrivalLaw n) =
        Measure.map (fun x : ℝ => Real.exp (-theta * value i) * x)
          (Measure.map (Function.eval i) (gumbelArrivalLaw n)) := by
      simpa [gumbelRaceTime, Function.comp_def] using
        (Measure.map_map (μ := gumbelArrivalLaw n)
          (g := fun x : ℝ => Real.exp (-theta * value i) * x)
          (f := Function.eval i)
          (measurable_const.mul measurable_id) (measurable_pi_apply i)).symm
    _ = (expMeasure 1).map (fun x : ℝ => Real.exp (-theta * value i) * x) := by
      rw [hpres.map_eq]

/-- The actual finite iid exponential source law has no race-time ties.  This
uses independence of product coordinates and atomlessness of each positively
scaled exponential marginal; it is not inferred from the target sequential
PMF. -/
theorem gumbelRaceNoTies {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) :
    GumbelRaceNoTies theta value := by
  let source : Measure (Candidate n → ℝ) := gumbelArrivalLaw n
  let raceCoordinate : Candidate n → (Candidate n → ℝ) → ℝ := fun i arrival =>
    gumbelRaceTime theta value arrival i
  have hprob : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := fun _ =>
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : ∀ _ : Candidate n, IsProbabilityMeasure (expMeasure 1) := hprob
  letI : IsProbabilityMeasure source := by
    simpa [source] using gumbelArrivalLaw_isProbabilityMeasure n
  have hcoordinate_measurable : ∀ i : Candidate n, Measurable (raceCoordinate i) := by
    intro i
    simpa [raceCoordinate] using gumbelRaceCoordinate_measurable theta value i
  have hindependent : iIndepFun raceCoordinate source := by
    change iIndepFun
      (fun i arrival =>
        (fun x : ℝ => Real.exp (-theta * value i) * x) (arrival i))
      (Measure.pi (fun _ : Candidate n => expMeasure 1))
    exact @iIndepFun_pi
      (Candidate n) inferInstance
      (fun _ => ℝ) (fun _ => inferInstance)
      (fun _ => expMeasure 1) hprob
      (fun _ => ℝ) (fun _ => inferInstance)
      (fun i x => Real.exp (-theta * value i) * x)
      (fun _ => (measurable_const.mul measurable_id).aemeasurable)
  have hpair : ∀ i j : Candidate n,
      ∀ᵐ arrival ∂source, i ≠ j → raceCoordinate i arrival ≠ raceCoordinate j arrival := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Filter.Eventually.of_forall fun _ hne => False.elim (hne rfl)
    · have hindependent_pair : raceCoordinate i ⟂ᵢ[source] raceCoordinate j :=
        hindependent.indepFun hij
      have hmap_pair :
          Measure.map (fun arrival => (raceCoordinate i arrival, raceCoordinate j arrival))
            source =
            (Measure.map (raceCoordinate i) source).prod
              (Measure.map (raceCoordinate j) source) := by
        exact (indepFun_iff_map_prod_eq_prod_map_map
          (hcoordinate_measurable i).aemeasurable
          (hcoordinate_measurable j).aemeasurable).mp hindependent_pair
      have hmap_j :
          Measure.map (raceCoordinate j) source =
            (expMeasure 1).map (fun x : ℝ => Real.exp (-theta * value j) * x) := by
        simpa [source, raceCoordinate] using
          gumbelRaceCoordinate_map_eq_scaledExponential theta value j
      letI : NoAtoms (Measure.map (raceCoordinate j) source) := by
        rw [hmap_j]
        exact scaledExponentialMeasure_noAtoms (Real.exp_pos _)
      have hdiagonal :
          (Measure.map (raceCoordinate i) source).prod
              (Measure.map (raceCoordinate j) source)
            {pair : ℝ × ℝ | pair.1 = pair.2} = 0 :=
        prod_real_diagonal_measure_zero
          (Measure.map (raceCoordinate i) source)
          (Measure.map (raceCoordinate j) source)
      have hevent : source
          {arrival | raceCoordinate i arrival = raceCoordinate j arrival} = 0 := by
        calc
          source {arrival | raceCoordinate i arrival = raceCoordinate j arrival} =
              Measure.map
                (fun arrival => (raceCoordinate i arrival, raceCoordinate j arrival)) source
                {pair : ℝ × ℝ | pair.1 = pair.2} := by
            rw [Measure.map_apply
              ((hcoordinate_measurable i).prodMk (hcoordinate_measurable j))
              (isClosed_eq continuous_fst continuous_snd).measurableSet]
            rfl
          _ = (Measure.map (raceCoordinate i) source).prod
              (Measure.map (raceCoordinate j) source)
                {pair : ℝ × ℝ | pair.1 = pair.2} := by rw [hmap_pair]
          _ = 0 := hdiagonal
      exact (measure_eq_zero_iff_ae_notMem.1 hevent).mono fun arrival hnot _ => hnot
  change ∀ᵐ arrival ∂source, ∀ i j : Candidate n, i ≠ j →
    raceCoordinate i arrival ≠ raceCoordinate j arrival
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  exact hpair i j

/-- A strict exponential-race cell: the candidates listed by `ranking` have
strictly increasing transformed arrival times. -/
def strictGumbelRaceCell {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    Set (Candidate n → ℝ) :=
  {arrival | ∀ p q : Candidate n, p < q →
    gumbelRaceTime theta value arrival (ranking p) <
      gumbelRaceTime theta value arrival (ranking q)}

/-- The strict-order cell for a vector of heterogeneous exponential race
times.  This is intentionally independent of the Gumbel construction. -/
def strictExponentialRaceOrderCell {n : ℕ} (ranking : Ranking n) :
    Set (Candidate n → ℝ) :=
  {time | ∀ p q : Candidate n, p < q →
    time (ranking p) < time (ranking q)}

theorem measurableSet_strictExponentialRaceOrderCell {n : ℕ}
    (ranking : Ranking n) :
    MeasurableSet (strictExponentialRaceOrderCell ranking) := by
  rw [show strictExponentialRaceOrderCell ranking =
      ⋂ p : Candidate n, ⋂ q : Candidate n,
        if p < q then
          {time : Candidate n → ℝ | time (ranking p) < time (ranking q)}
        else Set.univ by
      ext time
      simp [strictExponentialRaceOrderCell]]
  apply MeasurableSet.iInter
  intro p
  apply MeasurableSet.iInter
  intro q
  by_cases hpq : p < q
  · simpa [hpq] using
      (measurableSet_lt (measurable_pi_apply (ranking p))
        (measurable_pi_apply (ranking q)))
  · simp [hpq]

theorem strictGumbelRaceCell_eq_preimage_exponentialOrderCell {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    strictGumbelRaceCell theta value ranking =
      (gumbelRaceVector theta value) ⁻¹'
        strictExponentialRaceOrderCell ranking := by
  rfl

/-- The Gumbel strict-cell probability is exactly the corresponding
heterogeneous exponential strict-order probability.  Consequently the one
remaining bridge field is a standalone finite competing-exponentials theorem,
with no unproved distributional identification hidden in the Gumbel model. -/
theorem gumbelStrictRaceCell_probability_eq_exponentialOrderCell {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    gumbelArrivalLaw n (strictGumbelRaceCell theta value ranking) =
      (Measure.pi (fun i : Candidate n =>
        expMeasure (plackettLuceWeight theta value i)))
        (strictExponentialRaceOrderCell ranking) := by
  rw [strictGumbelRaceCell_eq_preimage_exponentialOrderCell]
  rw [← Measure.map_apply (measurable_gumbelRaceVector theta value)
    (measurableSet_strictExponentialRaceOrderCell ranking)]
  rw [gumbelRaceVector_law]

/-- The exact remaining finite analytic formula.  Its left side is a literal
product measure of independent exponentials with the displayed positive
rates, and its right side is the independently constructed sequential PMF.
No Gumbel-to-Plackett--Luce identification is built into this proposition. -/
def HasFiniteExponentialRaceOrderFormula {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) : Prop :=
  ∀ ranking : Ranking n,
    (Measure.pi (fun i : Candidate n =>
      expMeasure (plackettLuceWeight theta value i)))
      (strictExponentialRaceOrderCell ranking) =
        plackettLuceRankingPMF theta value ranking

/-- At an arrival vector with positive coordinates and no race ties, the
totalized score ranking event is exactly the strict exponential-race order
event.  This is a deterministic statement; the probability calculation is
kept separate. -/
private theorem scaleOneGumbelRank_eq_iff_strict_race_order_of_positive_noTies
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (arrival : Candidate n → ℝ) (ranking : Ranking n)
    (hpositive : ∀ i : Candidate n, 0 < arrival i)
    (hnoRaceTies : ∀ i j : Candidate n, i ≠ j →
      gumbelRaceTime theta value arrival i ≠
        gumbelRaceTime theta value arrival j) :
    scaleOneGumbelRank theta value arrival = ranking ↔
      ∀ p q : Candidate n, p < q →
        gumbelRaceTime theta value arrival (ranking p) <
          gumbelRaceTime theta value arrival (ranking q) := by
  have hscoreNoTies : ∀ i j : Candidate n, i ≠ j →
      scaleOneGumbelScores theta value arrival i ≠
        scaleOneGumbelScores theta value arrival j := by
    intro i j hij hscore
    have hscore' :
        -Real.log (gumbelRaceTime theta value arrival i) =
          -Real.log (gumbelRaceTime theta value arrival j) := by
      rw [← scaleOneGumbelScore_eq_neg_log_raceTime theta value arrival i (hpositive i),
        ← scaleOneGumbelScore_eq_neg_log_raceTime theta value arrival j (hpositive j)]
      exact hscore
    have hlog : Real.log (gumbelRaceTime theta value arrival i) =
        Real.log (gumbelRaceTime theta value arrival j) := by
      linarith
    apply hnoRaceTies i j hij
    have hexp := congrArg Real.exp hlog
    simpa [Real.exp_log (gumbelRaceTime_pos theta value arrival i (hpositive i)),
      Real.exp_log (gumbelRaceTime_pos theta value arrival j (hpositive j))] using hexp
  change rankByScore (scaleOneGumbelScores theta value arrival) = ranking ↔ _
  constructor
  · intro hrank p q hpq
    have hscore :=
      (rankByScore_eq_iff_strict_ranking_order_of_noTies
        (scaleOneGumbelScores theta value arrival) ranking hscoreNoTies).mp hrank p q hpq
    exact (scaleOneGumbelScore_lt_iff_raceTime_gt theta value arrival
      (ranking q) (ranking p) (hpositive (ranking q)) (hpositive (ranking p))).mp hscore
  · intro hrace
    apply
      (rankByScore_eq_iff_strict_ranking_order_of_noTies
        (scaleOneGumbelScores theta value arrival) ranking hscoreNoTies).mpr
    intro p q hpq
    exact (scaleOneGumbelScore_lt_iff_raceTime_gt theta value arrival
      (ranking q) (ranking p) (hpositive (ranking q)) (hpositive (ranking p))).mpr
      (hrace p q hpq)

/-- The literal total score-ranking event agrees almost everywhere with its
strict exponential-race cell under the actual iid exponential source law. -/
theorem scaleOneGumbelRank_event_ae_eq_strictGumbelRaceCell {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) (ranking : Ranking n) :
    (fun arrival => scaleOneGumbelRank theta value arrival = ranking) =ᵐ[gumbelArrivalLaw n]
      fun arrival => arrival ∈ strictGumbelRaceCell theta value ranking := by
  filter_upwards [gumbelArrivalLaw_ae_positive (n := n), gumbelRaceNoTies theta value]
    with arrival hpositive hnoRaceTies
  simpa [strictGumbelRaceCell] using
    (scaleOneGumbelRank_eq_iff_strict_race_order_of_positive_noTies
      theta value arrival ranking hpositive hnoRaceTies)

/-- An auditable source-semantic Gumbel/Plackett--Luce certificate over the
actual iid exponential product law.  The first two fields are proved above;
`strict_cell_probability` is the remaining finite competing-exponentials
calculation and cannot be discharged by identifying the target PMF in a
definition. -/
structure GumbelRaceCertificate {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ) : Prop where
  no_ties : GumbelRaceNoTies theta value
  ranking_event_ae : ∀ ranking : Ranking n,
    (fun arrival =>
      scaleOneGumbelRank theta value arrival = ranking) =ᵐ[gumbelArrivalLaw n]
        fun arrival => arrival ∈ strictGumbelRaceCell theta value ranking
  strict_cell_probability : ∀ ranking : Ranking n,
    gumbelArrivalLaw n (strictGumbelRaceCell theta value ranking) =
      plackettLuceRankingPMF theta value ranking

/-- The strict-cell probability calculation is now the only remaining field
needed for the full Gumbel/Plackett--Luce certificate: positive support,
atomlessness, and the ranking-event geometry are proved above from the actual
iid exponential source law. -/
theorem gumbelRaceCertificate_of_strict_cell_probability {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (hcell : ∀ ranking : Ranking n,
      gumbelArrivalLaw n (strictGumbelRaceCell theta value ranking) =
        plackettLuceRankingPMF theta value ranking) :
    GumbelRaceCertificate theta value :=
  { no_ties := gumbelRaceNoTies theta value
    ranking_event_ae := scaleOneGumbelRank_event_ae_eq_strictGumbelRaceCell theta value
    strict_cell_probability := hcell }

/-- Discharging the explicit finite exponential-race ordering formula yields
the Gumbel certificate without any additional probabilistic premise. -/
theorem gumbelRaceCertificate_of_exponentialOrderFormula {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (hformula : HasFiniteExponentialRaceOrderFormula theta value) :
    GumbelRaceCertificate theta value :=
  gumbelRaceCertificate_of_strict_cell_probability theta value fun ranking => by
    rw [gumbelStrictRaceCell_probability_eq_exponentialOrderCell]
    exact hformula ranking

/-- Once the explicitly named exponential-race certificate is proved, the
actual iid scale-one Gumbel RUM ranking PMF equals the independently defined
sequential Plackett--Luce PMF. -/
theorem scaleOneGumbelRUMRankingPMF_eq_plackettLuce_of_certificate {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (certificate : GumbelRaceCertificate theta value) :
    scaleOneGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF theta value := by
  letI : IsProbabilityMeasure (gumbelArrivalLaw n) :=
    gumbelArrivalLaw_isProbabilityMeasure n
  apply PMF.ext
  intro ranking
  change
    (rankingPMFOfMeasure (gumbelArrivalLaw n)
      (scaleOneGumbelRank theta value)
      (measurable_scaleOneGumbelRank theta value) ranking) =
      plackettLuceRankingPMF theta value ranking
  apply (ENNReal.toReal_eq_toReal_iff'
    ((rankingPMFOfMeasure (gumbelArrivalLaw n)
      (scaleOneGumbelRank theta value)
      (measurable_scaleOneGumbelRank theta value)).apply_ne_top ranking)
    ((plackettLuceRankingPMF theta value).apply_ne_top ranking)).mp
  rw [← pmfProb_singleton
    (rankingPMFOfMeasure (gumbelArrivalLaw n)
      (scaleOneGumbelRank theta value)
      (measurable_scaleOneGumbelRank theta value)) ranking]
  rw [rankingPMFOfMeasure_eventProb
    (gumbelArrivalLaw n) (scaleOneGumbelRank theta value)
    (measurable_scaleOneGumbelRank theta value)
    (fun rho : Ranking n => rho = ranking)]
  unfold measureProb
  have hEvents :
      {arrival | scaleOneGumbelRank theta value arrival = ranking} =ᵐ[gumbelArrivalLaw n]
        strictGumbelRaceCell theta value ranking :=
    certificate.ranking_event_ae ranking
  rw [measure_congr hEvents]
  exact congrArg ENNReal.toReal (certificate.strict_cell_probability ranking)

/-- The actual iid scale-one Gumbel RUM ranking PMF equals the independent
Plackett--Luce PMF once the remaining finite exponential strict-cell formula
is supplied. -/
theorem scaleOneGumbelRUMRankingPMF_eq_plackettLuce_of_strict_cell_probability {n : ℕ}
    (theta : ℝ) (value : Candidate n → ℝ)
    (hcell : ∀ ranking : Ranking n,
      gumbelArrivalLaw n (strictGumbelRaceCell theta value ranking) =
        plackettLuceRankingPMF theta value ranking) :
    scaleOneGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF theta value :=
  scaleOneGumbelRUMRankingPMF_eq_plackettLuce_of_certificate theta value
    (gumbelRaceCertificate_of_strict_cell_probability theta value hcell)

/-- For the repository's explicit scaled Gumbel convention, a proof of the
same race certificate at inverse temperature `theta / (sqrt 6 / pi)` yields
the corresponding Plackett--Luce law.  Identifying this convention with the
paper's unit-variance Gumbel model is a separate source-model bridge. -/
theorem unitVarianceGumbelRUMRankingPMF_eq_plackettLuce_of_certificate {n : ℕ}
    {theta : ℝ} (htheta : 0 < theta) (value : Candidate n → ℝ)
    (certificate : GumbelRaceCertificate
      (theta / unitVarianceGumbelScale) value) :
    unitVarianceGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value := by
  rw [unitVarianceGumbelRUMRankingPMF_eq_scaleOne htheta value]
  exact scaleOneGumbelRUMRankingPMF_eq_plackettLuce_of_certificate _ _ certificate

end KR21Monoculture

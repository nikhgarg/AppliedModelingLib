import Mathlib.Data.Sym.Card
import FalahatgarEtAl2017MaxingRanking.BordaProbability
import FalahatgarEtAl2017MaxingRanking.CanonicalComparisonBatches
import FalahatgarEtAl2017MaxingRanking.SampleBudget
import FalahatgarEtAl2017MaxingRanking.StrongTransitivityRanking

/-!
# Canonical batches for Strong-Transitivity-Ranking

Appendix B.2's Algorithm 6 samples every *unordered distinct* pair once,
then records the reverse comparison estimate by complementation.  This file
uses `Sym2 Arm` (with its diagonal removed) as the literal index of those
source batches, rather than replacing the source procedure by two independent
ordered-pair batches.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open AppliedModelingLib.Probability
open MeasureTheory ProbabilityTheory

/-- The unordered distinct arm pairs sampled by Algorithm 7. -/
abbrev StrongTransitivityPairIndex (Arm : Type*) [DecidableEq Arm] :=
  { pair : Sym2 Arm // ¬ pair.IsDiag }

/-- One fixed orientation of a source unordered pair, used only to run its
single Bernoulli batch.  Reversing this orientation does not change which
pair is sampled; it only determines which empirical estimate is complemented. -/
noncomputable def strongTransitivityPairFirst {Arm : Type*} [DecidableEq Arm]
    (pair : StrongTransitivityPairIndex Arm) : Arm :=
  pair.val.out.1

/-- The other endpoint of the oriented representative of a source pair. -/
noncomputable def strongTransitivityPairSecond {Arm : Type*} [DecidableEq Arm]
    (pair : StrongTransitivityPairIndex Arm) : Arm :=
  pair.val.out.2

/-- The two endpoints of every Algorithm-7 pair index are distinct. -/
theorem strongTransitivityPairFirst_ne_second {Arm : Type*} [DecidableEq Arm]
    (pair : StrongTransitivityPairIndex Arm) :
    strongTransitivityPairFirst pair ≠ strongTransitivityPairSecond pair := by
  intro hsame
  apply pair.property
  rw [← pair.val.out_eq]
  exact Sym2.mk_isDiag_iff.mpr hsame

/-- Algorithm 6's natural-number ceiling budget at the Algorithm-7
per-unordered-pair confidence `delta / n^2`.  Its `epsilon` argument is the
Algorithm-6 bias; Algorithm 7 supplies `epsilon / 2` here. -/
noncomputable def strongTransitivitySampleBudget
    (armCount : ℕ) (epsilon delta : ℝ) : ℕ :=
  fixedSampleBudget 0 epsilon (delta / (armCount : ℝ) ^ 2)

/-- The single product PMF containing every source unordered-pair batch. -/
noncomputable def canonicalStrongTransitivityBatchLaw {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) :
    PMF (StrongTransitivityPairIndex Arm →
      Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool) := by
  let batchSize := strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta
  let marginal : StrongTransitivityPairIndex Arm → Measure (Fin batchSize → Bool) := fun pair =>
    (canonicalComparisonBatchLaw preferenceGap hprobability
      (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair) batchSize).toMeasure
  letI : ∀ pair : StrongTransitivityPairIndex Arm,
      IsProbabilityMeasure (marginal pair) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  exact (Measure.pi marginal).toPMF

/-- The canonical Algorithm-7 PMF has exactly the intended heterogeneous
product measure over its unordered-pair batches. -/
theorem canonicalStrongTransitivityBatchLaw_toMeasure {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) :
    (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta).toMeasure =
      Measure.pi (fun pair : StrongTransitivityPairIndex Arm =>
        (canonicalComparisonBatchLaw preferenceGap hprobability
          (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair)
          (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta)).toMeasure) := by
  classical
  let batchSize := strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta
  let marginal : StrongTransitivityPairIndex Arm → Measure (Fin batchSize → Bool) := fun pair =>
    (canonicalComparisonBatchLaw preferenceGap hprobability
      (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair) batchSize).toMeasure
  letI : ∀ pair : StrongTransitivityPairIndex Arm,
      IsProbabilityMeasure (marginal pair) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi marginal) := by infer_instance
  change (Measure.pi marginal).toPMF.toMeasure = Measure.pi marginal
  exact Measure.toPMF_toMeasure _

/-- The full sampled batch for a given unordered pair has its declared
canonical Bernoulli law as its marginal. -/
theorem map_canonicalStrongTransitivityBatchCoordinate {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) (pair : StrongTransitivityPairIndex Arm) :
    Measure.map (fun batchTable => batchTable pair)
      (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta).toMeasure =
        (canonicalComparisonBatchLaw preferenceGap hprobability
          (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair)
          (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta)).toMeasure := by
  rw [canonicalStrongTransitivityBatchLaw_toMeasure]
  let batchSize := strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta
  let marginal : StrongTransitivityPairIndex Arm → Measure (Fin batchSize → Bool) := fun index =>
    (canonicalComparisonBatchLaw preferenceGap hprobability
      (strongTransitivityPairFirst index) (strongTransitivityPairSecond index) batchSize).toMeasure
  letI : ∀ index : StrongTransitivityPairIndex Arm,
      IsProbabilityMeasure (marginal index) := fun _ => inferInstance
  change Measure.map (fun batchTable => batchTable pair) (Measure.pi marginal) = marginal pair
  exact (measurePreserving_eval marginal pair).map_eq

/-- Algorithm 7 makes one Algorithm-6 batch for each unordered distinct
pair, so this is its literal (non-random) comparison count. -/
noncomputable def strongTransitivityComparisonCount {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] (epsilon delta : ℝ) : ℕ :=
  Fintype.card (StrongTransitivityPairIndex Arm) *
    strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta

/-- The unordered-pair carrier has the exact binomial count expected from
Algorithm 7. -/
theorem strongTransitivityPairIndex_card {Arm : Type*} [Fintype Arm] [DecidableEq Arm] :
    Fintype.card (StrongTransitivityPairIndex Arm) = (Fintype.card Arm).choose 2 :=
  Sym2.card_subtype_not_diag

/-- Expanding the definition makes Algorithm 7's exact one-batch-per-pair
comparison cost explicit. -/
theorem strongTransitivityComparisonCount_eq {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm] (epsilon delta : ℝ) :
    strongTransitivityComparisonCount (Arm := Arm) epsilon delta =
      (Fintype.card Arm).choose 2 *
        strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta := by
  rw [strongTransitivityComparisonCount, strongTransitivityPairIndex_card]

/-- The centered empirical gap reported by Algorithm 6 for the fixed
orientation of one unordered pair. -/
noncomputable def strongTransitivityPairEmpiricalGap {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (epsilon delta : ℝ) (pair : StrongTransitivityPairIndex Arm)
    (batch : Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool) : ℝ :=
  bordaEmpiricalScore
    (fun sampleIndex outcome =>
      canonicalComparisonBatchObservation
        (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta)
        sampleIndex outcome)
    (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) batch - 1 / 2

/-- The Algorithm-6 ceiling budget makes the two-sided empirical centered-gap
tail at most its Algorithm-7 per-pair confidence. -/
theorem strongTransitivitySampleBudget_tail_le_pairConfidence
    (armCount : ℕ) (epsilon delta : ℝ)
    (hcard : 0 < armCount) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    2 * Real.exp (-((strongTransitivitySampleBudget armCount epsilon delta : ℝ) *
      (epsilon / 2)) ^ 2 /
      (2 * (strongTransitivitySampleBudget armCount epsilon delta : ℝ) * (1 / 4 : ℝ))) ≤
        delta / (armCount : ℝ) ^ 2 := by
  have hcardReal : 0 < (armCount : ℝ) := by exact_mod_cast hcard
  have hcardGeOne : 1 ≤ (armCount : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcard)
  have hcardSqPos : 0 < (armCount : ℝ) ^ 2 := sq_pos_of_pos hcardReal
  have hcardSqGeOne : 1 ≤ (armCount : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((armCount : ℝ) - 1)]
  have heta : 0 < delta / (armCount : ℝ) ^ 2 := div_pos hdelta hcardSqPos
  have hetaLeOne : delta / (armCount : ℝ) ^ 2 ≤ 1 := by
    have hle : delta / (armCount : ℝ) ^ 2 ≤ delta := by
      apply (div_le_iff₀ hcardSqPos).mpr
      nlinarith
    exact hle.trans hdeltaLeOne
  change
    2 * Real.exp (-((fixedSampleBudget 0 epsilon
      (delta / (armCount : ℝ) ^ 2) : ℝ) * (epsilon / 2)) ^ 2 /
      (2 * (fixedSampleBudget 0 epsilon (delta / (armCount : ℝ) ^ 2) : ℝ) *
        (1 / 4 : ℝ))) ≤ delta / (armCount : ℝ) ^ 2
  simpa using (fixedSampleCompare_tail_le_delta_of_ceilingBudget 0 epsilon
    (delta / (armCount : ℝ) ^ 2) hepsilon heta hetaLeOne)

/-- Lemma 19 for the literal fixed orientation of one source unordered pair:
Algorithm 6 estimates its centered preference to error `epsilon / 2` at the
Algorithm-7 per-pair confidence. -/
theorem strongTransitivityPairEmpiricalGap_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) (pair : StrongTransitivityPairIndex Arm)
    (hcard : 0 < Fintype.card Arm) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (canonicalComparisonBatchLaw preferenceGap hprobability
      (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair)
      (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
        {batch | ¬ |strongTransitivityPairEmpiricalGap epsilon delta pair batch -
          preferenceGap (strongTransitivityPairFirst pair)
            (strongTransitivityPairSecond pair)| < epsilon / 2} ≤
      delta / (Fintype.card Arm : ℝ) ^ 2 := by
  let batchSize := strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta
  let observation : ℕ → (Fin batchSize → Bool) → ℝ := fun sampleIndex batch =>
    canonicalComparisonBatchObservation batchSize sampleIndex batch
  have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hcardSqPos : 0 < (Fintype.card Arm : ℝ) ^ 2 := sq_pos_of_pos hcardReal
  have heta : 0 < delta / (Fintype.card Arm : ℝ) ^ 2 := div_pos hdelta hcardSqPos
  have hetaLeOne : delta / (Fintype.card Arm : ℝ) ^ 2 ≤ 1 := by
    have hcardGeOne : 1 ≤ (Fintype.card Arm : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcard)
    have hcardSqGeOne : 1 ≤ (Fintype.card Arm : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((Fintype.card Arm : ℝ) - 1)]
    have hle : delta / (Fintype.card Arm : ℝ) ^ 2 ≤ delta := by
      apply (div_le_iff₀ hcardSqPos).mpr
      nlinarith
    exact hle.trans hdeltaLeOne
  have hbatchPosReal : 0 < (batchSize : ℝ) := by
    dsimp [batchSize, strongTransitivitySampleBudget]
    exact fixedSampleBudget_pos 0 epsilon (delta / (Fintype.card Arm : ℝ) ^ 2)
      hepsilon heta hetaLeOne
  have hbatchPos : 0 < batchSize := by exact_mod_cast hbatchPosReal
  have htail := bordaEmpiricalScore_nonconcentration_probability
    (canonicalComparisonBatchLaw preferenceGap hprobability
      (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair) batchSize).toMeasure
    observation batchSize
    (1 / 2 + preferenceGap (strongTransitivityPairFirst pair)
      (strongTransitivityPairSecond pair)) (epsilon / 2) hbatchPos
    (by
      simpa [observation] using iIndepFun_canonicalComparisonBatchObservation
        preferenceGap hprobability (strongTransitivityPairFirst pair)
          (strongTransitivityPairSecond pair) batchSize)
    (by
      intro sampleIndex hsampleIndex
      exact measurable_canonicalComparisonBatchObservation batchSize sampleIndex)
    (by
      intro sampleIndex hsampleIndex
      exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
        (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair)
        batchSize sampleIndex)
    (by
      intro sampleIndex hsampleIndex
      exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
        (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair)
        batchSize sampleIndex hsampleIndex)
    (by linarith)
  have hevent : {batch | ¬ |strongTransitivityPairEmpiricalGap epsilon delta pair batch -
      preferenceGap (strongTransitivityPairFirst pair)
        (strongTransitivityPairSecond pair)| < epsilon / 2} =
      {batch | ¬ |bordaEmpiricalScore observation batchSize batch -
        (1 / 2 + preferenceGap (strongTransitivityPairFirst pair)
          (strongTransitivityPairSecond pair))| < epsilon / 2} := by
    ext batch
    simp only [Set.mem_setOf_eq]
    change ¬ |bordaEmpiricalScore observation batchSize batch - 1 / 2 -
      preferenceGap (strongTransitivityPairFirst pair)
        (strongTransitivityPairSecond pair)| < epsilon / 2 ↔
      ¬ |bordaEmpiricalScore observation batchSize batch -
        (1 / 2 + preferenceGap (strongTransitivityPairFirst pair)
          (strongTransitivityPairSecond pair))| < epsilon / 2
    ring_nf
  rw [hevent]
  calc
    _ ≤ 2 * Real.exp (-((batchSize : ℝ) * (epsilon / 2)) ^ 2 /
        (2 * (batchSize : ℝ) * (1 / 4 : ℝ))) := htail
    _ ≤ delta / (Fintype.card Arm : ℝ) ^ 2 := by
      dsimp [batchSize]
      exact strongTransitivitySampleBudget_tail_le_pairConfidence
        (Fintype.card Arm) epsilon delta hcard hepsilon hdelta hdeltaLeOne

/-- Reading one Algorithm-6 empirical estimate from the complete product
outcome. -/
noncomputable def canonicalStrongTransitivityPairEmpiricalGap {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (epsilon delta : ℝ)
    (batchTable : StrongTransitivityPairIndex Arm →
      Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool)
    (pair : StrongTransitivityPairIndex Arm) : ℝ :=
  strongTransitivityPairEmpiricalGap epsilon delta pair (batchTable pair)

/-- The Lemma-19 tail survives as the corresponding coordinate event under
the one joint Algorithm-7 product law. -/
theorem canonicalStrongTransitivityPairEmpiricalGap_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) (pair : StrongTransitivityPairIndex Arm)
    (hcard : 0 < Fintype.card Arm) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta).toMeasure.real
        {batchTable | ¬
          |canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
            preferenceGap (strongTransitivityPairFirst pair)
              (strongTransitivityPairSecond pair)| < epsilon / 2} ≤
      delta / (Fintype.card Arm : ℝ) ^ 2 := by
  let failureEvent : Set (Fin (strongTransitivitySampleBudget
      (Fintype.card Arm) epsilon delta) → Bool) := {batch | ¬
    |strongTransitivityPairEmpiricalGap epsilon delta pair batch -
      preferenceGap (strongTransitivityPairFirst pair)
        (strongTransitivityPairSecond pair)| < epsilon / 2}
  have hfailureMeasurable : MeasurableSet failureEvent := MeasurableSet.of_discrete
  have hpreimage : {batchTable | ¬
      |canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
        preferenceGap (strongTransitivityPairFirst pair)
          (strongTransitivityPairSecond pair)| < epsilon / 2} =
      (fun batchTable => batchTable pair) ⁻¹' failureEvent := by
    ext batchTable
    simp [canonicalStrongTransitivityPairEmpiricalGap, failureEvent]
  calc
    (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta).toMeasure.real
        {batchTable | ¬
          |canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
            preferenceGap (strongTransitivityPairFirst pair)
              (strongTransitivityPairSecond pair)| < epsilon / 2} =
        (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta).toMeasure.real
          ((fun batchTable => batchTable pair) ⁻¹' failureEvent) := by rw [hpreimage]
    _ = (Measure.map (fun batchTable => batchTable pair)
          (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta).toMeasure).real
          failureEvent := by
        simp only [measureReal_def]
        rw [Measure.map_apply (measurable_pi_apply pair) hfailureMeasurable]
    _ = (canonicalComparisonBatchLaw preferenceGap hprobability
          (strongTransitivityPairFirst pair) (strongTransitivityPairSecond pair)
          (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
          failureEvent := by
        rw [map_canonicalStrongTransitivityBatchCoordinate preferenceGap hprobability
          epsilon delta pair]
    _ ≤ delta / (Fintype.card Arm : ℝ) ^ 2 := by
        exact strongTransitivityPairEmpiricalGap_failure_probability preferenceGap hprobability
          epsilon delta pair hcard hepsilon hdelta hdeltaLeOne

/-- The source unordered-pair index induced by two distinct arms. -/
noncomputable def strongTransitivityPairOfNe {Arm : Type*} [DecidableEq Arm]
    (first second : Arm) (hne : first ≠ second) : StrongTransitivityPairIndex Arm :=
  ⟨s(first, second), by simpa using hne⟩

/-- A pair index is represented by its selected oriented endpoints. -/
theorem strongTransitivityPair_repr {Arm : Type*} [DecidableEq Arm]
    (pair : StrongTransitivityPairIndex Arm) :
    s(strongTransitivityPairFirst pair, strongTransitivityPairSecond pair) = pair.val :=
  pair.val.out_eq

/-- Swapping distinct arms gives the same source unordered-pair batch index. -/
theorem strongTransitivityPairOfNe_swap {Arm : Type*} [DecidableEq Arm]
    (first second : Arm) (hne : first ≠ second) :
    strongTransitivityPairOfNe first second hne =
      strongTransitivityPairOfNe second first hne.symm := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- The complete centered estimate table read by Algorithm 7: the one sampled
orientation is used directly and the reverse entry is its negative, which is
the centered form of the source assignment `pHat[j,i] = 1 - pHat[i,j]`. -/
noncomputable def canonicalStrongTransitivityRankingEstimate {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (epsilon delta : ℝ)
    (batchTable : StrongTransitivityPairIndex Arm →
      Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool)
    (first second : Arm) : ℝ :=
  if hsame : first = second then 0
  else
    let pair := strongTransitivityPairOfNe first second hsame
    if first = strongTransitivityPairFirst pair then
      canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair
    else
      -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair

/-- Algorithm 7's centered diagonal estimate is exactly zero. -/
theorem canonicalStrongTransitivityRankingEstimate_self {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (epsilon delta : ℝ)
    (batchTable : StrongTransitivityPairIndex Arm →
      Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool)
    (arm : Arm) :
    canonicalStrongTransitivityRankingEstimate epsilon delta batchTable arm arm = 0 := by
  simp [canonicalStrongTransitivityRankingEstimate]

/-- If all literal unordered-pair batches are accurate in their sampled
orientation, complementing the reverse entries gives Algorithm 7's required
simultaneous accuracy event for the complete centered estimate table. -/
theorem pairwiseEstimateAccurate_canonicalStrongTransitivityRankingEstimate
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (batchTable : StrongTransitivityPairIndex Arm →
      Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hepsilon : 0 < epsilon)
    (hpairAccurate : ∀ pair : StrongTransitivityPairIndex Arm,
      |canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
        preferenceGap (strongTransitivityPairFirst pair)
          (strongTransitivityPairSecond pair)| < epsilon / 2) :
    PairwiseEstimateAccurate preferenceGap
      (canonicalStrongTransitivityRankingEstimate epsilon delta batchTable) epsilon := by
  intro first second
  by_cases hsame : first = second
  · subst second
    rw [canonicalStrongTransitivityRankingEstimate_self, hself]
    simp
    linarith
  · let pair := strongTransitivityPairOfNe first second hsame
    have horient :
        s(strongTransitivityPairFirst pair, strongTransitivityPairSecond pair) =
          s(first, second) := by
      calc
        s(strongTransitivityPairFirst pair, strongTransitivityPairSecond pair) = pair.val :=
          strongTransitivityPair_repr pair
        _ = s(first, second) := rfl
    rcases Sym2.eq_iff.mp horient with horiented | hswapped
    · have hforward : first = strongTransitivityPairFirst pair := horiented.1.symm
      rw [canonicalStrongTransitivityRankingEstimate, dif_neg hsame]
      change |(if first = strongTransitivityPairFirst pair then
        canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair else
        -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair) -
          preferenceGap first second| < epsilon / 2
      rw [if_pos hforward]
      simpa [horiented.1, horiented.2] using hpairAccurate pair
    · have hnotForward : first ≠ strongTransitivityPairFirst pair := by
        intro hforward
        apply hsame
        calc
          first = strongTransitivityPairFirst pair := hforward
          _ = second := hswapped.1
      have hgap : preferenceGap (strongTransitivityPairFirst pair)
          (strongTransitivityPairSecond pair) = -preferenceGap first second := by
        rw [hswapped.1, hswapped.2]
        exact hantisymmetric first second
      rw [canonicalStrongTransitivityRankingEstimate, dif_neg hsame]
      change |(if first = strongTransitivityPairFirst pair then
        canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair else
        -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair) -
          preferenceGap first second| < epsilon / 2
      rw [if_neg hnotForward]
      have hrewrite :
          -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
              preferenceGap first second =
            -(canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
              preferenceGap (strongTransitivityPairFirst pair)
                (strongTransitivityPairSecond pair)) := by
        rw [hgap]
        ring
      rw [hrewrite, abs_neg]
      exact hpairAccurate pair

/-- A good literal batch for the one unordered pair containing two distinct
arms gives the corresponding directed table entry's accuracy. -/
theorem canonicalStrongTransitivityRankingEstimate_accuracy_of_pair
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (batchTable : StrongTransitivityPairIndex Arm →
      Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (first second : Arm) (hne : first ≠ second)
    (hpairAccurate :
      |canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable
          (strongTransitivityPairOfNe first second hne) -
        preferenceGap
          (strongTransitivityPairFirst (strongTransitivityPairOfNe first second hne))
          (strongTransitivityPairSecond (strongTransitivityPairOfNe first second hne))|
        < epsilon / 2) :
    |canonicalStrongTransitivityRankingEstimate epsilon delta batchTable first second -
      preferenceGap first second| < epsilon / 2 := by
  let pair := strongTransitivityPairOfNe first second hne
  have horient :
      s(strongTransitivityPairFirst pair, strongTransitivityPairSecond pair) =
        s(first, second) := by
    calc
      s(strongTransitivityPairFirst pair, strongTransitivityPairSecond pair) = pair.val :=
        strongTransitivityPair_repr pair
      _ = s(first, second) := rfl
  rcases Sym2.eq_iff.mp horient with horiented | hswapped
  · have hforward : first = strongTransitivityPairFirst pair := horiented.1.symm
    rw [canonicalStrongTransitivityRankingEstimate, dif_neg hne]
    change |(if first = strongTransitivityPairFirst pair then
      canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair else
      -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair) -
        preferenceGap first second| < epsilon / 2
    rw [if_pos hforward]
    simpa [pair, horiented.1, horiented.2] using hpairAccurate
  · have hnotForward : first ≠ strongTransitivityPairFirst pair := by
      intro hforward
      apply hne
      calc
        first = strongTransitivityPairFirst pair := hforward
        _ = second := hswapped.1
    have hgap : preferenceGap (strongTransitivityPairFirst pair)
        (strongTransitivityPairSecond pair) = -preferenceGap first second := by
      rw [hswapped.1, hswapped.2]
      exact hantisymmetric first second
    rw [canonicalStrongTransitivityRankingEstimate, dif_neg hne]
    change |(if first = strongTransitivityPairFirst pair then
      canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair else
      -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair) -
        preferenceGap first second| < epsilon / 2
    rw [if_neg hnotForward]
    have hrewrite :
        -canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
            preferenceGap first second =
          -(canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable pair -
            preferenceGap (strongTransitivityPairFirst pair)
              (strongTransitivityPairSecond pair)) := by
      rw [hgap]
      ring
    rw [hrewrite, abs_neg]
    simpa [pair] using hpairAccurate

/-- Every directed estimate used by Algorithm 7 has failure probability at
most `delta / n^2` under the one canonical unordered-pair product law.  The
diagonal is deterministic; a non-diagonal direction is controlled by its
single sampled unordered pair and, if necessary, the source complement rule. -/
theorem canonicalStrongTransitivityRankingEstimate_failure_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hcard : 0 < Fintype.card Arm) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (pair : Arm × Arm) :
    pmfProbClassical
      (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta)
      (PairwiseEstimateFailure preferenceGap
        (fun batchTable =>
          canonicalStrongTransitivityRankingEstimate epsilon delta batchTable) epsilon pair) ≤
      delta / (Fintype.card (Arm × Arm) : ℝ) := by
  classical
  let law := canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta
  have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hcardSqPos : 0 < (Fintype.card Arm : ℝ) ^ 2 := sq_pos_of_pos hcardReal
  have hbound : law.toMeasure.real
      {batchTable | ¬
        |canonicalStrongTransitivityRankingEstimate epsilon delta batchTable pair.1 pair.2 -
          preferenceGap pair.1 pair.2| < epsilon / 2} ≤
      delta / (Fintype.card Arm : ℝ) ^ 2 := by
    by_cases hsame : pair.1 = pair.2
    · have hself : preferenceGap pair.1 pair.1 = 0 := by
        have hanti := hantisymmetric pair.1 pair.1
        linarith
      have hempty : {batchTable | ¬
          |canonicalStrongTransitivityRankingEstimate epsilon delta batchTable pair.1 pair.2 -
            preferenceGap pair.1 pair.2| < epsilon / 2} = ∅ := by
        rw [hsame.symm]
        ext batchTable
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        rw [canonicalStrongTransitivityRankingEstimate_self, hself]
        simp
        linarith
      rw [hempty]
      simp [le_of_lt (div_pos hdelta hcardSqPos)]
    · let sourcePair := strongTransitivityPairOfNe pair.1 pair.2 hsame
      let sourceFailure : Set
          (StrongTransitivityPairIndex Arm →
            Fin (strongTransitivitySampleBudget (Fintype.card Arm) epsilon delta) → Bool) :=
        {batchTable | ¬
          |canonicalStrongTransitivityPairEmpiricalGap epsilon delta batchTable sourcePair -
            preferenceGap (strongTransitivityPairFirst sourcePair)
              (strongTransitivityPairSecond sourcePair)| < epsilon / 2}
      have hsubset : {batchTable | ¬
          |canonicalStrongTransitivityRankingEstimate epsilon delta batchTable pair.1 pair.2 -
            preferenceGap pair.1 pair.2| < epsilon / 2} ⊆ sourceFailure := by
        intro batchTable hfailure
        simp only [Set.mem_setOf_eq] at hfailure ⊢
        by_contra hsourceAccurate
        simp only [sourceFailure, Set.mem_setOf_eq, not_not] at hsourceAccurate
        apply hfailure
        exact canonicalStrongTransitivityRankingEstimate_accuracy_of_pair
          preferenceGap epsilon delta batchTable hantisymmetric pair.1 pair.2 hsame
          (by simpa [sourcePair] using hsourceAccurate)
      calc
        law.toMeasure.real {batchTable | ¬
            |canonicalStrongTransitivityRankingEstimate epsilon delta batchTable pair.1 pair.2 -
              preferenceGap pair.1 pair.2| < epsilon / 2} ≤ law.toMeasure.real sourceFailure :=
          measureReal_mono hsubset (measure_ne_top _ _)
        _ ≤ delta / (Fintype.card Arm : ℝ) ^ 2 := by
          simpa [law, sourceFailure, sourcePair] using
            (canonicalStrongTransitivityPairEmpiricalGap_failure_probability
              preferenceGap hprobability epsilon delta sourcePair
              hcard hepsilon hdelta hdeltaLeOne)
  rw [pmfProbClassical_eq_pmfProb, AppliedModelingLib.pmfProb_eq_toMeasure_real]
  change law.toMeasure.real
      {batchTable | ¬
        |canonicalStrongTransitivityRankingEstimate epsilon delta batchTable pair.1 pair.2 -
          preferenceGap pair.1 pair.2| < epsilon / 2} ≤
      delta / (Fintype.card (Arm × Arm) : ℝ)
  simpa [Fintype.card_prod, Nat.cast_mul, pow_two] using hbound

/-- Lemma 20's high-probability conclusion for the literal Algorithm-6/7
execution: one finite PMF samples every unordered pair once, fills reverse
estimates by the source complement rule, and the concrete threshold recursion
returns an `epsilon`-ranking with probability at least `1 - delta`. -/
theorem canonicalStrongTransitivityRankingOutput_highProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (sourceRanking : Fin (Fintype.card Arm) → Arm)
    (hsourceRanking : PreferenceRanking preferenceGap sourceRanking)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hcard : 0 < Fintype.card Arm) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta ≤ pmfProbClassical
      (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta)
      (fun batchTable => EpsilonPreferenceRanking preferenceGap epsilon
        (strongTransitivityRankingOutput
          (canonicalStrongTransitivityRankingEstimate epsilon delta batchTable) epsilon)) := by
  apply strongTransitivityRankingOutput_success_probability_of_pairEstimateGuarantees
    (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta)
    preferenceGap
    (fun batchTable =>
      canonicalStrongTransitivityRankingEstimate epsilon delta batchTable)
    epsilon delta sourceRanking hsourceRanking
  intro pair
  exact canonicalStrongTransitivityRankingEstimate_failure_probability
    preferenceGap hprobability epsilon delta hantisymmetric hcard hepsilon hdelta hdeltaLeOne pair

end FalahatgarEtAl2017MaxingRanking

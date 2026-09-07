import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Math.EpsilonContinuity
import AppliedModelingLib.SocialChoice.Ranking.Basic
import AppliedModelingLib.SocialChoice.Ranking.Kendall
import AppliedModelingLib.SocialChoice.Ranking.Score

/-!
# Probability Laws on Rankings

Reusable bridges between measure-theoretic random rankings and finite PMF laws
on ranking spaces.

## Main declarations

- `rankingPMFOfMeasure`
- `rankingPMFOfMeasure_eventProb`
- `rankingPMFOfMeasure_atom_epsilonContinuousAt_of_source_event`
- `bestRemainingAfterProb_rankingPMFOfMeasure`
- `firstChoiceProb`
- `firstChoiceProb_rankingPMFOfMeasure`
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- Rankings carry the discrete measurable structure by default. -/
instance instMeasurableSpaceRanking (n : ℕ) : MeasurableSpace (Ranking n) := ⊤

/-- Probability that a ranking law places candidate `c` first. -/
def firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  AppliedModelingLib.pmfProb μ (fun π => c = firstChoice π)

/--
First-choice events for distinct candidates are disjoint, so their probabilities
have total mass at most one.
-/
theorem firstChoiceProb_add_le_one {n : ℕ}
    (μ : PMF (Ranking n)) {c d : Candidate n} (hcd : c ≠ d) :
    firstChoiceProb μ c + firstChoiceProb μ d ≤ 1 := by
  classical
  have hdisjoint :
      ∀ π : Ranking n,
        c = firstChoice π → d = firstChoice π → False := by
    intro π hc hd
    exact hcd (hc.trans hd.symm)
  have hunion :
      AppliedModelingLib.pmfProb μ
          (fun π : Ranking n => c = firstChoice π ∨ d = firstChoice π) =
        firstChoiceProb μ c + firstChoiceProb μ d := by
    simpa [firstChoiceProb] using
      (AppliedModelingLib.pmfProb_or_eq_add_of_disjoint μ
        (fun π : Ranking n => c = firstChoice π)
        (fun π : Ranking n => d = firstChoice π)
        hdisjoint)
  rw [← hunion]
  exact AppliedModelingLib.pmfProb_le_one μ
    (fun π : Ranking n => c = firstChoice π ∨ d = firstChoice π)

/--
The ranking PMF induced by pushing a probability measure through a ranking map.
-/
def rankingPMFOfMeasure
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank) : PMF (Ranking n) :=
  @MeasureTheory.Measure.toPMF (Ranking n) _ _ _ (μ.map rank)
    (MeasureTheory.Measure.isProbabilityMeasure_map hrank.aemeasurable)

/--
The event that measurable finite score coordinates sort to a fixed ranking is
measurable.

The proof expands `Tuple.sort`: a fixed permutation is selected exactly when
the permuted score tuple is weakly sorted, with deterministic tie-breaking.
Thus each atom is a finite Boolean combination of coordinate inequalities.
-/
theorem measurableSet_rankByScore_eq
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Candidate n → ℝ)
    (hscore : ∀ c : Candidate n, Measurable (fun ω => score ω c))
    (π : Ranking n) :
    MeasurableSet
      {ω | rankByScore (score ω) = π} := by
  classical
  let sortedEvent : Set Ω :=
    {ω |
      Monotone ((fun c : Candidate n => -score ω c) ∘ π) ∧
        ∀ i j : Candidate n, i < j →
          ((fun c : Candidate n => -score ω c) ∘ π) i =
            ((fun c : Candidate n => -score ω c) ∘ π) j →
          π i < π j}
  have hset :
      {ω | rankByScore (score ω) = π} = sortedEvent := by
    ext ω
    constructor
    · intro h
      have hπ :
          π = Tuple.sort (fun c : Candidate n => -score ω c) := by
        simpa [rankByScore] using h.symm
      exact (Tuple.eq_sort_iff (f := fun c : Candidate n => -score ω c)
        (σ := π)).mp hπ
    · intro h
      have hπ :
          π = Tuple.sort (fun c : Candidate n => -score ω c) :=
        (Tuple.eq_sort_iff (f := fun c : Candidate n => -score ω c)
          (σ := π)).mpr h
      simpa [rankByScore] using hπ.symm
  have hmono :
      MeasurableSet
        {ω |
          Monotone ((fun c : Candidate n => -score ω c) ∘ π)} := by
    have hmono' :
        MeasurableSet
          (⋂ i : Candidate n, ⋂ j : Candidate n,
            {ω |
              i ≤ j → -score ω (π i) ≤ -score ω (π j)}) :=
      MeasurableSet.iInter fun i : Candidate n =>
        MeasurableSet.iInter fun j : Candidate n => by
        by_cases hij : i ≤ j
        · simpa [hij] using
            measurableSet_le ((hscore (π i)).neg) ((hscore (π j)).neg)
        · simp [hij]
    rw [show
      {ω |
        Monotone ((fun c : Candidate n => -score ω c) ∘ π)} =
      (⋂ i : Candidate n, ⋂ j : Candidate n,
        {ω |
          i ≤ j → -score ω (π i) ≤ -score ω (π j)}) by
        ext ω
        simp [Monotone]]
    exact hmono'
  have htie :
      MeasurableSet
        {ω |
          ∀ i j : Candidate n, i < j →
            ((fun c : Candidate n => -score ω c) ∘ π) i =
              ((fun c : Candidate n => -score ω c) ∘ π) j →
            π i < π j} := by
    have htie' :
        MeasurableSet
          (⋂ i : Candidate n, ⋂ j : Candidate n,
            {ω |
              i < j →
                ((fun c : Candidate n => -score ω c) ∘ π) i =
                  ((fun c : Candidate n => -score ω c) ∘ π) j →
                π i < π j}) :=
      MeasurableSet.iInter fun i : Candidate n =>
        MeasurableSet.iInter fun j : Candidate n => by
        by_cases hij : i < j
        · by_cases hpij : π i < π j
          · simp [hij, hpij]
          · rw [show
              {ω |
                i < j →
                  ((fun c : Candidate n => -score ω c) ∘ π) i =
                    ((fun c : Candidate n => -score ω c) ∘ π) j →
                  π i < π j} =
              {ω | -score ω (π i) = -score ω (π j)}ᶜ by
                ext ω
                simp [hij, hpij]]
            exact (measurableSet_eq_fun ((hscore (π i)).neg)
              ((hscore (π j)).neg)).compl
        · simp [hij]
    rw [show
      {ω |
        ∀ i j : Candidate n, i < j →
          ((fun c : Candidate n => -score ω c) ∘ π) i =
            ((fun c : Candidate n => -score ω c) ∘ π) j →
          π i < π j} =
      (⋂ i : Candidate n, ⋂ j : Candidate n,
        {ω |
          i < j →
            ((fun c : Candidate n => -score ω c) ∘ π) i =
              ((fun c : Candidate n => -score ω c) ∘ π) j →
            π i < π j}) by
        ext ω
        simp]
    exact htie'
  rw [hset]
  exact hmono.inter htie

/--
Measurability of the finite ranking obtained by sorting measurable score
coordinates.
-/
theorem measurable_rankByScore
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (score : Ω → Candidate n → ℝ)
    (hscore : ∀ c : Candidate n, Measurable (fun ω => score ω c)) :
    Measurable (fun ω => rankByScore (score ω)) := by
  classical
  exact measurable_to_countable' fun π =>
    measurableSet_rankByScore_eq score hscore π

/--
Event probabilities for an induced ranking PMF are source-measure preimage
masses.
-/
theorem rankingPMFOfMeasure_eventProb
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (p : Ranking n → Prop) [DecidablePred p] :
    AppliedModelingLib.pmfProb (rankingPMFOfMeasure μ rank hrank) p =
      AppliedModelingLib.measureProb μ (fun ω => p (rank ω)) := by
  unfold rankingPMFOfMeasure
  exact AppliedModelingLib.pmfProb_toPMF_map_eq_measureProb
    μ rank hrank p MeasurableSet.of_discrete

/--
If the source probability of any inversion relative to a reference ranking is
less than `δ`, then the induced finite ranking law is atomwise `δ`-close to the
pure law at that reference ranking.
-/
theorem rankingPMFOfMeasure_atomwise_close_to_pure_of_inversion_prob_lt
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (center : Ranking n) {δ : ℝ} (hδ : 0 < δ)
    (hinv :
      AppliedModelingLib.measureProb μ
          (fun ω =>
            ∃ ab : Candidate n × Candidate n,
              invertedPair center (rank ω) ab) < δ) :
    ∀ π : Ranking n,
      |((rankingPMFOfMeasure μ rank hrank) π).toReal -
          (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  classical
  have hwrong_source :
      AppliedModelingLib.measureProb μ (fun ω => rank ω ≠ center) < δ := by
    exact lt_of_le_of_lt
      (AppliedModelingLib.measureProb_mono μ
        (fun ω => rank ω ≠ center)
        (fun ω =>
          ∃ ab : Candidate n × Candidate n,
            invertedPair center (rank ω) ab)
        (fun ω hwrong => exists_invertedPair_of_ne hwrong))
      hinv
  have hwrong_pmf :
      AppliedModelingLib.pmfProb (rankingPMFOfMeasure μ rank hrank)
          (fun π => π ≠ center) < δ := by
    rw [rankingPMFOfMeasure_eventProb μ rank hrank
      (fun π : Ranking n => π ≠ center)]
    exact hwrong_source
  exact
    AppliedModelingLib.atomwise_close_to_pure_of_wrong_prob_lt
      (rankingPMFOfMeasure μ rank hrank) center hδ hwrong_pmf

/--
Union-bound form: if the sum of the source probabilities of all pairwise
inversions relative to a reference ranking is less than `δ`, then the induced
ranking law is atomwise `δ`-close to the pure reference law.
-/
theorem rankingPMFOfMeasure_atomwise_close_to_pure_of_sum_inversion_probs_lt
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (center : Ranking n) {δ : ℝ} (hδ : 0 < δ)
    (hsum :
      (∑ ab : Candidate n × Candidate n,
        AppliedModelingLib.measureProb μ
          (fun ω => invertedPair center (rank ω) ab)) < δ) :
    ∀ π : Ranking n,
      |((rankingPMFOfMeasure μ rank hrank) π).toReal -
          (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  classical
  refine rankingPMFOfMeasure_atomwise_close_to_pure_of_inversion_prob_lt
    μ rank hrank center hδ ?_
  calc
    AppliedModelingLib.measureProb μ
        (fun ω =>
          ∃ ab : Candidate n × Candidate n,
            invertedPair center (rank ω) ab)
        =
      AppliedModelingLib.measureProb μ
        (fun ω =>
          ∃ ab ∈ (Finset.univ : Finset (Candidate n × Candidate n)),
            invertedPair center (rank ω) ab) := by
        congr 1
        funext ω
        simp
    _ ≤
      ∑ ab ∈ (Finset.univ : Finset (Candidate n × Candidate n)),
        AppliedModelingLib.measureProb μ
          (fun ω => invertedPair center (rank ω) ab) :=
        AppliedModelingLib.measureProb_biUnion_finset_le μ
          (Finset.univ : Finset (Candidate n × Candidate n))
          (fun ab ω => invertedPair center (rank ω) ab)
    _ =
      ∑ ab : Candidate n × Candidate n,
        AppliedModelingLib.measureProb μ
          (fun ω => invertedPair center (rank ω) ab) := by
        simp
    _ < δ := hsum

/--
Adjacent union-bound form: if the sum of the source probabilities of adjacent
inversions in the reference order is less than `δ`, then the induced ranking
law is atomwise `δ`-close to the pure reference law.
-/
theorem rankingPMFOfMeasure_atomwise_close_to_pure_of_sum_adjacent_inversion_probs_lt
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (center : Ranking n) {δ : ℝ} (hδ : 0 < δ)
    (hsum :
      (∑ i : Fin (n + 1),
        AppliedModelingLib.measureProb μ
          (fun ω => invertedPair center (rank ω)
            (center i.castSucc, center i.succ))) < δ) :
    ∀ π : Ranking n,
      |((rankingPMFOfMeasure μ rank hrank) π).toReal -
          (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  classical
  have hwrong_source :
      AppliedModelingLib.measureProb μ (fun ω => rank ω ≠ center) < δ := by
    calc
      AppliedModelingLib.measureProb μ (fun ω => rank ω ≠ center)
          ≤
        AppliedModelingLib.measureProb μ
          (fun ω =>
            ∃ i : Fin (n + 1),
              invertedPair center (rank ω)
                (center i.castSucc, center i.succ)) := by
          exact AppliedModelingLib.measureProb_mono μ
            (fun ω => rank ω ≠ center)
            (fun ω =>
              ∃ i : Fin (n + 1),
                invertedPair center (rank ω)
                  (center i.castSucc, center i.succ))
            (fun ω hwrong => exists_adjacent_invertedPair_of_ne hwrong)
      _ =
        AppliedModelingLib.measureProb μ
          (fun ω =>
            ∃ i ∈ (Finset.univ : Finset (Fin (n + 1))),
              invertedPair center (rank ω)
                (center i.castSucc, center i.succ)) := by
          congr 1
          funext ω
          simp
      _ ≤
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
          AppliedModelingLib.measureProb μ
            (fun ω => invertedPair center (rank ω)
              (center i.castSucc, center i.succ)) :=
          AppliedModelingLib.measureProb_biUnion_finset_le μ
            (Finset.univ : Finset (Fin (n + 1)))
            (fun i ω => invertedPair center (rank ω)
              (center i.castSucc, center i.succ))
      _ =
        ∑ i : Fin (n + 1),
          AppliedModelingLib.measureProb μ
            (fun ω => invertedPair center (rank ω)
              (center i.castSucc, center i.succ)) := by
          simp
      _ < δ := hsum
  have hwrong_pmf :
      AppliedModelingLib.pmfProb (rankingPMFOfMeasure μ rank hrank)
          (fun π => π ≠ center) < δ := by
    rw [rankingPMFOfMeasure_eventProb μ rank hrank
      (fun π : Ranking n => π ≠ center)]
    exact hwrong_source
  exact
    AppliedModelingLib.atomwise_close_to_pure_of_wrong_prob_lt
      (rankingPMFOfMeasure μ rank hrank) center hδ hwrong_pmf

/--
Score-gap form of the adjacent union bound: if the total source probability of
adjacent true-neighbor score misorders is less than `δ`, then the score-induced
ranking law is atomwise `δ`-close to the pure reference law.
-/
theorem rankingPMFOfMeasure_rankByScore_atomwise_close_to_pure_of_sum_adjacent_score_misorder_probs_lt
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (score : Ω → Candidate n → ℝ)
    (hrank : Measurable (fun ω => rankByScore (score ω)))
    (center : Ranking n) {δ : ℝ} (hδ : 0 < δ)
    (hsum :
      (∑ i : Fin (n + 1),
        AppliedModelingLib.measureProb μ
          (fun ω => score ω (center i.castSucc) ≤ score ω (center i.succ))) < δ) :
    ∀ π : Ranking n,
      |((rankingPMFOfMeasure μ
            (fun ω => rankByScore (score ω)) hrank) π).toReal -
          (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  classical
  refine
    rankingPMFOfMeasure_atomwise_close_to_pure_of_sum_adjacent_inversion_probs_lt
      μ (fun ω => rankByScore (score ω)) hrank center hδ ?_
  have hle :
      (∑ i : Fin (n + 1),
        AppliedModelingLib.measureProb μ
          (fun ω =>
            invertedPair center (rankByScore (score ω))
              (center i.castSucc, center i.succ))) ≤
      ∑ i : Fin (n + 1),
        AppliedModelingLib.measureProb μ
          (fun ω => score ω (center i.castSucc) ≤ score ω (center i.succ)) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact AppliedModelingLib.measureProb_mono μ
      (fun ω =>
        invertedPair center (rankByScore (score ω))
          (center i.castSucc, center i.succ))
      (fun ω => score ω (center i.castSucc) ≤ score ω (center i.succ))
      (fun ω hinv =>
        score_le_of_invertedPair_rankByScore
          (center := center) (score := score ω)
          (ab := (center i.castSucc, center i.succ)) hinv)
  exact lt_of_le_of_lt hle hsum

/--
Asymptotic union-bound form: if the total source probability of pairwise
inversions relative to a reference ranking tends to zero, then the induced
ranking law gets arbitrarily atomwise close to the pure reference law at
sufficiently high accuracy.
-/
theorem rankingPMFOfMeasure_atomwise_concentration_of_sum_inversion_probs_tendsto
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℝ → MeasureTheory.Measure Ω)
    [∀ θ, MeasureTheory.IsProbabilityMeasure (μ θ)]
    (rank : ℝ → Ω → Ranking n)
    (hrank : ∀ θ, Measurable (rank θ))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun θ : ℝ =>
          ∑ ab : Candidate n × Candidate n,
            AppliedModelingLib.measureProb (μ θ)
              (fun ω => invertedPair center (rank θ ω) ab))
        Filter.atTop (nhds 0)) :
    ∀ lower δ, 0 < δ →
      ∃ hi, lower < hi ∧
        ∀ π : Ranking n,
          |((rankingPMFOfMeasure (μ hi) (rank hi) (hrank hi)) π).toReal -
            (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  intro lower δ hδ
  have hsmall :
      ∀ᶠ θ : ℝ in Filter.atTop,
        (∑ ab : Candidate n × Candidate n,
          AppliedModelingLib.measureProb (μ θ)
            (fun ω => invertedPair center (rank θ ω) ab)) < δ :=
    hsum.eventually (Iio_mem_nhds hδ)
  rcases Filter.eventually_atTop.1
      (hsmall.and (Filter.eventually_gt_atTop lower)) with
    ⟨hi, hhi⟩
  refine ⟨hi, (hhi hi le_rfl).2, ?_⟩
  exact
    rankingPMFOfMeasure_atomwise_close_to_pure_of_sum_inversion_probs_lt
      (μ hi) (rank hi) (hrank hi) center hδ (hhi hi le_rfl).1

/--
Asymptotic adjacent union-bound form: if the total source probability of
adjacent inversions in the reference order tends to zero, then the induced
ranking law gets arbitrarily atomwise close to the pure reference law at
sufficiently high accuracy.
-/
theorem rankingPMFOfMeasure_atomwise_concentration_of_sum_adjacent_inversion_probs_tendsto
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℝ → MeasureTheory.Measure Ω)
    [∀ θ, MeasureTheory.IsProbabilityMeasure (μ θ)]
    (rank : ℝ → Ω → Ranking n)
    (hrank : ∀ θ, Measurable (rank θ))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun θ : ℝ =>
          ∑ i : Fin (n + 1),
            AppliedModelingLib.measureProb (μ θ)
              (fun ω => invertedPair center (rank θ ω)
                (center i.castSucc, center i.succ)))
        Filter.atTop (nhds 0)) :
    ∀ lower δ, 0 < δ →
      ∃ hi, lower < hi ∧
        ∀ π : Ranking n,
          |((rankingPMFOfMeasure (μ hi) (rank hi) (hrank hi)) π).toReal -
            (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  intro lower δ hδ
  have hsmall :
      ∀ᶠ θ : ℝ in Filter.atTop,
        (∑ i : Fin (n + 1),
          AppliedModelingLib.measureProb (μ θ)
            (fun ω => invertedPair center (rank θ ω)
              (center i.castSucc, center i.succ))) < δ :=
    hsum.eventually (Iio_mem_nhds hδ)
  rcases Filter.eventually_atTop.1
      (hsmall.and (Filter.eventually_gt_atTop lower)) with
    ⟨hi, hhi⟩
  refine ⟨hi, (hhi hi le_rfl).2, ?_⟩
  exact
    rankingPMFOfMeasure_atomwise_close_to_pure_of_sum_adjacent_inversion_probs_lt
      (μ hi) (rank hi) (hrank hi) center hδ (hhi hi le_rfl).1

/--
Asymptotic score-gap form: if the total probability of adjacent true-neighbor
score misorders tends to zero, then the induced score-ranking law gets
arbitrarily atomwise close to the pure reference law.
-/
theorem rankingPMFOfMeasure_rankByScore_atomwise_concentration_of_sum_adjacent_score_misorder_probs_tendsto
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℝ → MeasureTheory.Measure Ω)
    [∀ θ, MeasureTheory.IsProbabilityMeasure (μ θ)]
    (score : ℝ → Ω → Candidate n → ℝ)
    (hrank : ∀ θ, Measurable (fun ω => rankByScore (score θ ω)))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun θ : ℝ =>
          ∑ i : Fin (n + 1),
            AppliedModelingLib.measureProb (μ θ)
              (fun ω =>
                score θ ω (center i.castSucc) ≤
                  score θ ω (center i.succ)))
        Filter.atTop (nhds 0)) :
    ∀ lower δ, 0 < δ →
      ∃ hi, lower < hi ∧
        ∀ π : Ranking n,
          |((rankingPMFOfMeasure (μ hi)
              (fun ω => rankByScore (score hi ω)) (hrank hi)) π).toReal -
            (((PMF.pure center : PMF (Ranking n)) π).toReal)| < δ := by
  intro lower δ hδ
  have hsmall :
      ∀ᶠ θ : ℝ in Filter.atTop,
        (∑ i : Fin (n + 1),
          AppliedModelingLib.measureProb (μ θ)
            (fun ω =>
              score θ ω (center i.castSucc) ≤
                score θ ω (center i.succ))) < δ :=
    hsum.eventually (Iio_mem_nhds hδ)
  rcases Filter.eventually_atTop.1
      (hsmall.and (Filter.eventually_gt_atTop lower)) with
    ⟨hi, hhi⟩
  refine ⟨hi, (hhi hi le_rfl).2, ?_⟩
  exact
    rankingPMFOfMeasure_rankByScore_atomwise_close_to_pure_of_sum_adjacent_score_misorder_probs_lt
      (μ hi) (score hi) (hrank hi) center hδ (hhi hi le_rfl).1

/--
Finite expectations under an induced ranking law are source integrals of the
corresponding pointwise ranking payoff.
-/
theorem rankingPMFOfMeasure_pmfExp_eq_integral
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (payoff : Ranking n → ℝ) :
    AppliedModelingLib.pmfExp (rankingPMFOfMeasure μ rank hrank) payoff =
      ∫ ω, payoff (rank ω) ∂μ := by
  rw [AppliedModelingLib.pmfExp_eq_integral_toMeasure]
  unfold rankingPMFOfMeasure
  rw [MeasureTheory.Measure.toPMF_toMeasure]
  have hpayoff :
      MeasureTheory.AEStronglyMeasurable payoff
        (MeasureTheory.Measure.map rank μ) :=
    (measurable_of_finite payoff).aestronglyMeasurable
  simpa using
    (MeasureTheory.integral_map
      (μ := μ) (φ := rank) (f := payoff)
      hrank.aemeasurable hpayoff)

/--
If a measurable map transports the source measure and intertwines the ranking
maps, then the induced finite ranking laws are equal.
-/
theorem rankingPMFOfMeasure_eq_of_measurePreserving
    {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ν : MeasureTheory.Measure Ω') [MeasureTheory.IsProbabilityMeasure ν]
    (e : Ω → Ω') (he : MeasureTheory.MeasurePreserving e μ ν)
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (rank' : Ω' → Ranking n) (hrank' : Measurable rank')
    (hintertwine : ∀ ω, rank ω = rank' (e ω)) :
    rankingPMFOfMeasure μ rank hrank =
      rankingPMFOfMeasure ν rank' hrank' := by
  classical
  apply PMF.ext
  intro π
  apply (ENNReal.toReal_eq_toReal_iff'
    ((rankingPMFOfMeasure μ rank hrank).apply_ne_top π)
    ((rankingPMFOfMeasure ν rank' hrank').apply_ne_top π)).mp
  rw [← AppliedModelingLib.pmfProb_singleton (rankingPMFOfMeasure μ rank hrank) π]
  rw [← AppliedModelingLib.pmfProb_singleton (rankingPMFOfMeasure ν rank' hrank') π]
  rw [rankingPMFOfMeasure_eventProb μ rank hrank
    (fun ρ : Ranking n => ρ = π)]
  rw [rankingPMFOfMeasure_eventProb ν rank' hrank'
    (fun ρ : Ranking n => ρ = π)]
  trans AppliedModelingLib.measureProb μ (fun ω => rank' (e ω) = π)
  · congr 1
    funext ω
    rw [hintertwine ω]
  · exact AppliedModelingLib.measureProb_preimage_of_measurePreserving
      e he (fun ω' : Ω' => rank' ω' = π)
      (by
        simpa only [Set.preimage_setOf_eq] using
          hrank' (show MeasurableSet {ρ : Ranking n | ρ = π}
            from MeasurableSet.of_discrete))

/--
Atomwise continuity of source ranking-event probabilities transfers to the
finite PMF induced by a measurable ranking map.

This is a paper-neutral wrapper for continuous RUM arguments: the hard analytic
work is proving continuity of the source event mass; the finite ranking PMF
atom then follows by `rankingPMFOfMeasure_eventProb`.
-/
theorem rankingPMFOfMeasure_atom_epsilonContinuousAt_of_source_event
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {x : ℝ}
    (μ : ℝ → MeasureTheory.Measure Ω)
    [∀ θ, MeasureTheory.IsProbabilityMeasure (μ θ)]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (π : Ranking n)
    (hsource :
      AppliedModelingLib.EpsilonContinuousAt
        (fun θ => AppliedModelingLib.measureProb (μ θ)
          (fun ω => rank ω = π)) x) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun θ => (((rankingPMFOfMeasure (μ θ) rank hrank) π).toReal)) x := by
  have hpoint :
      (fun θ : ℝ => (((rankingPMFOfMeasure (μ θ) rank hrank) π).toReal)) =
        fun θ : ℝ => AppliedModelingLib.measureProb (μ θ)
          (fun ω => rank ω = π) := by
    funext θ
    rw [← AppliedModelingLib.pmfProb_singleton
      (rankingPMFOfMeasure (μ θ) rank hrank) π]
    exact rankingPMFOfMeasure_eventProb (μ θ) rank hrank
      (fun ρ : Ranking n => ρ = π)
  rw [hpoint]
  exact hsource

/--
If a parameterized source ranking is almost surely locally constant at `x`,
then every atom of the induced finite ranking law is continuous at `x`.

This is the reusable finite-valued part of continuous RUM arguments. The
remaining analytic work for a concrete source model is proving the local
stability statement, typically by showing that score ties have source measure
zero and that all score gaps vary continuously in the accuracy parameter.
-/
theorem rankingPMFOfMeasure_atom_epsilonContinuousAt_of_ae_eventually_eq
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : ℝ → Ω → Ranking n)
    (hrank : ∀ θ, Measurable (rank θ))
    {x : ℝ}
    (hstable :
      ∀ᵐ ω ∂μ, ∀ᶠ θ in nhds x, rank θ ω = rank x ω)
    (π : Ranking n) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun θ => (((rankingPMFOfMeasure μ (rank θ) (hrank θ)) π).toReal)) x := by
  classical
  let A : Set Ω := {ω | rank x ω = π}
  let As : ℝ → Set Ω := fun θ => {ω | rank θ ω = π}
  have hA : MeasurableSet A := by
    change MeasurableSet ((rank x) ⁻¹' ({π} : Set (Ranking n)))
    exact (hrank x) MeasurableSet.of_discrete
  have hAs : ∀ θ, MeasurableSet (As θ) := by
    intro θ
    change MeasurableSet ((rank θ) ⁻¹' ({π} : Set (Ranking n)))
    exact (hrank θ) MeasurableSet.of_discrete
  have hlim :
      ∀ᵐ ω ∂μ, ∀ᶠ θ in nhds x, (ω ∈ As θ ↔ ω ∈ A) := by
    filter_upwards [hstable] with ω hω
    filter_upwards [hω] with θ hθ
    simp [A, As, hθ]
  have htendsto_measure :
      Filter.Tendsto (fun θ => μ (As θ)) (nhds x) (nhds (μ A)) :=
    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (L := nhds x) hA hAs hlim
  have htendsto_real :
      ContinuousAt (fun θ => (μ (As θ)).toReal) x := by
    simpa [A, As] using
      (ENNReal.continuousAt_toReal (MeasureTheory.measure_ne_top μ A)).tendsto.comp
        htendsto_measure
  have hsource :
      AppliedModelingLib.EpsilonContinuousAt
        (fun θ => AppliedModelingLib.measureProb μ (fun ω => rank θ ω = π)) x := by
    exact AppliedModelingLib.epsilonContinuousAt_of_continuousAt (by simpa [AppliedModelingLib.measureProb, As] using htendsto_real)
  have hpoint :
      (fun θ : ℝ => (((rankingPMFOfMeasure μ (rank θ) (hrank θ)) π).toReal)) =
        fun θ : ℝ => AppliedModelingLib.measureProb μ (fun ω => rank θ ω = π) := by
    funext θ
    rw [← AppliedModelingLib.pmfProb_singleton
      (rankingPMFOfMeasure μ (rank θ) (hrank θ)) π]
    exact rankingPMFOfMeasure_eventProb μ (rank θ) (hrank θ)
      (fun ρ : Ranking n => ρ = π)
  rw [hpoint]
  exact hsource

/--
Continuous-measure form of the probability that, after removing one candidate,
the best remaining candidate is another fixed candidate.
-/
theorem bestRemainingAfterProb_rankingPMFOfMeasure
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (removed chosen : Candidate n) :
    AppliedModelingLib.pmfProb (rankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π removed = chosen) =
      AppliedModelingLib.measureProb μ
        (fun ω => bestRemainingAfter (rank ω) removed = chosen) := by
  exact rankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π removed = chosen)

/-- Continuous-measure form of first-choice probability. -/
theorem firstChoiceProb_rankingPMFOfMeasure
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (rank : Ω → Ranking n) (hrank : Measurable rank)
    (c : Candidate n) :
    firstChoiceProb (rankingPMFOfMeasure μ rank hrank) c =
      AppliedModelingLib.measureProb μ (fun ω => c = firstChoice (rank ω)) := by
  unfold firstChoiceProb
  exact rankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => c = firstChoice π)

end

end Ranking
end SocialChoice
end AppliedModelingLib

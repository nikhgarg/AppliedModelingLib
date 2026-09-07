import KR21Monoculture.MainTheorems

/-!
# Full Definition 1 removal monotonicity

The original source Definition 1 quantifies over every set of candidates left
after removals.  The older `Theorem1RemovalMonotonicityAt` package deliberately
keeps only the singleton-removal consequence consumed by the paper's Theorem 1
game proof.  This module exposes the stronger source-facing proposition
directly: every nonempty finite remaining set is weakly improved, and the full
candidate set is strictly improved.

The theorem results intentionally keep the `Finset` quantifier visible rather
than hiding it in a certificate structure.
-/

open AppliedModelingLib MeasureTheory
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/--
The full Definition 1 monotonicity conclusion for a source-coupled score
contraction.  `remaining` is the set left after the source's removed set has
been deleted, so `remaining.Nonempty` is exactly the proper-removal condition.
-/
theorem paper_definition1_full_removal_monotonicity_of_measure_rankByScore_contraction
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (raw : Ω → Candidate n → ℝ) {t : ℝ}
    (hrawRank :
      Measurable (fun omega =>
        rankByScore (raw omega)))
    (hcontractRank :
      Measurable (fun omega =>
        rankByScore
          (fun i => paper_appendixC_contractedScore t (F.value i) (raw omega i))))
    (hdistH :
      F.dist thetaH =
        rankingPMFOfMeasure mu
          (fun omega => rankByScore (raw omega))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        rankingPMFOfMeasure mu
          (fun omega =>
            rankByScore
              (fun i => paper_appendixC_contractedScore t (F.value i) (raw omega i)))
          hcontractRank)
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hstrict_univ :
      0 < mu {omega |
        F.value
          (bestInSet
            (rankByScore (raw omega))
            Finset.univ) <
        F.value
          (bestInSet
            (rankByScore
              (fun i => paper_appendixC_contractedScore t (F.value i) (raw omega i)))
            Finset.univ)}) :
    (∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining) ∧
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ := by
  classical
  constructor
  · intro remaining hremaining
    rw [hdistH, hdistA]
    exact
      paper_appendixA_expectedBestInSet_monotonicity_of_measure_rankByScore_contraction
        mu F.value raw hrawRank hcontractRank ht0 htlt1 hremaining
  · rw [hdistH, hdistA]
    have hremaining : (Finset.univ : Finset (Candidate n)).Nonempty :=
      ⟨0, Finset.mem_univ _⟩
    exact
      paper_appendixA_expectedBestInSet_strict_of_measure_rankByScore_contraction
        mu F.value raw hrawRank hcontractRank ht0 htlt1 hremaining hstrict_univ

/--
The full Definition 1 removal conclusion for the paper's literal scaled-noise
RUM source family.  This theorem makes the common source law, both ranking-law
equalities, the accuracy order, and the full-set strictness event explicit.
-/
theorem paper_definition1_full_removal_monotonicity_of_scaledNoise_rankByScore_source
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (noise : Ω → Candidate n → ℝ)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun omega =>
        rankByScore
          (fun i => F.value i + noise omega i / thetaH)))
    (haccurateRank :
      Measurable (fun omega =>
        rankByScore
          (fun i => F.value i + noise omega i / thetaA)))
    (hdistH :
      F.dist thetaH =
        rankingPMFOfMeasure mu
          (fun omega =>
            rankByScore
              (fun i => F.value i + noise omega i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        rankingPMFOfMeasure mu
          (fun omega =>
            rankByScore
              (fun i => F.value i + noise omega i / thetaA))
          haccurateRank)
    (hstrict_univ :
      0 < mu {omega |
        F.value
          (bestInSet
            (rankByScore
              (fun i => F.value i + noise omega i / thetaH))
            Finset.univ) <
        F.value
          (bestInSet
            (rankByScore
              (fun i => F.value i + noise omega i / thetaA))
            Finset.univ)}) :
    (∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining) ∧
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ := by
  classical
  have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
  let t : ℝ := thetaH / thetaA
  let raw : Ω → Candidate n → ℝ :=
    fun omega i => F.value i + noise omega i / thetaH
  have ht0 : 0 ≤ t := le_of_lt (div_pos hthetaH hthetaA)
  have htlt1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hthetaA).mpr hthetaHA
  have hcontract_eq :
      (fun omega =>
        rankByScore
          (fun i => paper_appendixC_contractedScore t (F.value i) (raw omega i))) =
      (fun omega =>
        rankByScore
          (fun i => F.value i + noise omega i / thetaA)) := by
    funext omega
    congr 1
    funext i
    simp [t, raw, paper_appendixC_contractedScore, rumContractScore,
      AppliedModelingLib.Probability.rumContractScore]
    field_simp [ne_of_gt hthetaH, ne_of_gt hthetaA]
  have hcontractRank :
      Measurable (fun omega =>
        rankByScore
          (fun i => paper_appendixC_contractedScore t (F.value i) (raw omega i))) := by
    rw [hcontract_eq]
    exact haccurateRank
  refine
    paper_definition1_full_removal_monotonicity_of_measure_rankByScore_contraction
      (F := F) (thetaA := thetaA) (thetaH := thetaH)
      mu raw hrawRank hcontractRank ?_ ?_ ht0 htlt1 ?_
  · simpa [raw] using hdistH
  · simpa [hcontract_eq] using hdistA
  · have hset :
        {omega |
          F.value
            (bestInSet
              (rankByScore (raw omega))
              Finset.univ) <
          F.value
            (bestInSet
              (rankByScore
                (fun i => paper_appendixC_contractedScore t (F.value i) (raw omega i)))
              Finset.univ)} =
          {omega |
            F.value
              (bestInSet
                (rankByScore
                  (fun i => F.value i + noise omega i / thetaH))
                Finset.univ) <
            F.value
              (bestInSet
                (rankByScore
                  (fun i => F.value i + noise omega i / thetaA))
                Finset.univ)} := by
      ext omega
      simp [raw, congrFun hcontract_eq omega]
    rw [hset]
    exact hstrict_univ

/--
The full Definition 1 removal conclusion under the source's positive
full-dimensional scaled-noise density model.  Full support derives the only
strictness event; no finite-removal conclusion is hidden behind a package.
-/
theorem paper_definition1_full_removal_monotonicity_of_scaledNoise_fullSupport_density
    {n : ℕ}
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (hmu :
      mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun noise : Candidate n → ℝ =>
        rankByScore
          (fun i => F.value i + noise i / thetaH)))
    (haccurateRank :
      Measurable (fun noise : Candidate n → ℝ =>
        rankByScore
          (fun i => F.value i + noise i / thetaA)))
    (hdistH :
      F.dist thetaH =
        rankingPMFOfMeasure mu
          (fun noise =>
            rankByScore
              (fun i => F.value i + noise i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        rankingPMFOfMeasure mu
          (fun noise =>
            rankByScore
              (fun i => F.value i + noise i / thetaA))
          haccurateRank)
    {low high : Candidate n}
    (hvalue : F.value low < F.value high) :
    (∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining) ∧
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ := by
  classical
  have hstrict_univ :
      0 < mu {noise |
        F.value
          (bestInSet
            (rankByScore
              (fun i => F.value i + noise i / thetaH))
            Finset.univ) <
        F.value
          (bestInSet
            (rankByScore
              (fun i => F.value i + noise i / thetaA))
            Finset.univ)} := by
    rw [hmu]
    simpa using
      paper_appendixA_scaledNoise_strict_fullset_improvement_pos_of_noise_fullSupport
        D hD hDpos F.value hthetaH hthetaHA hvalue
  exact
    paper_definition1_full_removal_monotonicity_of_scaledNoise_rankByScore_source
      (F := F) (thetaA := thetaA) (thetaH := thetaH)
      mu (fun noise c => noise c) hthetaH hthetaHA hrawRank haccurateRank
      hdistH hdistA hstrict_univ

end KR21Monoculture

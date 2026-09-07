import AppliedModelingLib.Learning.HumanFeedback.PairwiseCountExistence
import AppliedModelingLib.Foundations.Optimization.CompactPerturbation

/-!
# Source-specific finite counterexample datasets for pairwise MLE properties

This module records the integral realization of the rational-frequency
construction in Supplement E of Noothigattu--Peters--Procaccia (2020).  It is
deliberately only the discrete data layer: the source's existence, compactness,
continuity, and derivative analysis needed to show that its MLE ranks `b`
above `a` remain separate analytic obligations.
-/

namespace NoothigattuEtAl2020PairwiseComparisons

open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset
open AppliedModelingLib.Optimization

/--
The integral form of Supplement E's three-alternative dataset.  For a rational
perturbation `ε = numerator / denominator`, these are the source counts after
multiplication by `denominator`: `a ≻ b` and `a ≻ c` have count
`5 * denominator + numerator`, their reverses have count `5 * denominator`,
and the `b,c` comparison has counts `100 * denominator` and `denominator`.

The alternatives `0, 1, 2` stand for the source's `a, b, c`, respectively.
-/
def supplementETheorem5Dataset (numerator denominator : ℕ) :
    PairwiseCountDataset (Fin 3) where
  count := fun winner loser =>
    if winner.val = 0 ∧ loser.val = 1 then 5 * denominator + numerator else
    if winner.val = 1 ∧ loser.val = 0 then 5 * denominator else
    if winner.val = 0 ∧ loser.val = 2 then 5 * denominator + numerator else
    if winner.val = 2 ∧ loser.val = 0 then 5 * denominator else
    if winner.val = 1 ∧ loser.val = 2 then 100 * denominator else
    if winner.val = 2 ∧ loser.val = 1 then denominator else 0
  diagonal_zero := by
    intro alternative
    fin_cases alternative <;> simp

/-- The source labelling `a,b,c` is the canonical finite ranking `0,1,2`. -/
def supplementETheorem5Ranking : Fin 3 ≃ Fin (Fintype.card (Fin 3)) :=
  finCongr (by simp)

/-- The two source counts on `a,b` after rational-frequency scaling. -/
@[simp] theorem supplementETheorem5Dataset_count_a_b
    (numerator denominator : ℕ) :
    (supplementETheorem5Dataset numerator denominator).count 0 1 =
      5 * denominator + numerator := by
  simp [supplementETheorem5Dataset]

@[simp] theorem supplementETheorem5Dataset_count_b_a
    (numerator denominator : ℕ) :
    (supplementETheorem5Dataset numerator denominator).count 1 0 =
      5 * denominator := by
  simp [supplementETheorem5Dataset]

/-- The two source counts on `a,c` after rational-frequency scaling. -/
@[simp] theorem supplementETheorem5Dataset_count_a_c
    (numerator denominator : ℕ) :
    (supplementETheorem5Dataset numerator denominator).count 0 2 =
      5 * denominator + numerator := by
  simp [supplementETheorem5Dataset]

@[simp] theorem supplementETheorem5Dataset_count_c_a
    (numerator denominator : ℕ) :
    (supplementETheorem5Dataset numerator denominator).count 2 0 =
      5 * denominator := by
  simp [supplementETheorem5Dataset]

/-- The two source counts on `b,c` after rational-frequency scaling. -/
@[simp] theorem supplementETheorem5Dataset_count_b_c
    (numerator denominator : ℕ) :
    (supplementETheorem5Dataset numerator denominator).count 1 2 =
      100 * denominator := by
  simp [supplementETheorem5Dataset]

@[simp] theorem supplementETheorem5Dataset_count_c_b
    (numerator denominator : ℕ) :
    (supplementETheorem5Dataset numerator denominator).count 2 1 =
      denominator := by
  simp [supplementETheorem5Dataset]

/--
Every rational perturbation `ε = numerator / denominator` in `(0,1]` gives
the strict pairwise-count majorities `a ≻ b`, `a ≻ c`, and `b ≻ c` used in
Supplement E.  This is the exact discrete Definition-5.1 half of the source
counterexample, independent of the still-open MLE-order argument.
-/
theorem supplementETheorem5Dataset_hasPairwiseMajorityRanking
    {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hnumerator_le : numerator ≤ denominator) :
    (supplementETheorem5Dataset numerator denominator).hasPairwiseMajorityRanking
      supplementETheorem5Ranking := by
  intro first second hranking
  fin_cases first <;> fin_cases second <;>
    simp [supplementETheorem5Dataset, supplementETheorem5Ranking] at hranking ⊢
  all_goals omega

/-- The six ordered distinct pairs of the source's three alternatives. -/
private theorem supplementETheorem5_offDiag : (Finset.univ : Finset (Fin 3)).offDiag =
    ({(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)} : Finset (Fin 3 × Fin 3)) := by
  decide

/--
The two additional `a`-win log terms in the integral `ε = 1 / denominator`
Supplement-E dataset.  After dividing its likelihood by `denominator`, this
is precisely the `ε`-dependent part of the source objective.
-/
noncomputable def supplementETheorem5Perturbation
    (link : ℝ → ℝ) (score : ScoreVector (Fin 3)) : ℝ :=
  Real.log (link (score 0 - score 1)) + Real.log (link (score 0 - score 2))

/--
For the exact integral realization `ε = 1 / denominator`, the likelihood is
`denominator` times the `ε = 0` likelihood plus the two perturbing source
terms.  This lets the finite proof use a compact-gap argument directly,
without introducing nonintegral count data.
-/
theorem pairwiseLogLikelihood_supplementETheorem5_unitFraction
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3)) :
    pairwiseLogLikelihood (supplementETheorem5Dataset 1 denominator) link score =
      (denominator : ℝ) *
        pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link score +
          supplementETheorem5Perturbation link score := by
  classical
  unfold pairwiseLogLikelihood
  rw [supplementETheorem5_offDiag]
  simp [supplementETheorem5Dataset, supplementETheorem5Perturbation]
  unfold randomUtilityWinProbability
  ring

/-- The finite perturbation term is continuous under the source link hypotheses. -/
theorem continuous_supplementETheorem5Perturbation
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    Continuous (supplementETheorem5Perturbation link) := by
  rw [continuous_iff_continuousAt]
  intro score
  unfold supplementETheorem5Perturbation
  apply ContinuousAt.add
  · have hgap : ContinuousAt (fun candidate : ScoreVector (Fin 3) =>
        candidate 0 - candidate 1) score :=
      (continuousAt_apply 0 score).sub (continuousAt_apply 1 score)
    have hlink : ContinuousAt (link : ℝ → ℝ) (score 0 - score 1) :=
      hcontinuous.continuousAt
    have hlog : ContinuousAt (fun value : ℝ => Real.log (link value)) (score 0 - score 1) := by
      simpa only [Function.comp_apply] using
        (Real.continuousAt_log
          (ne_of_gt (link.openProbability hstrict (score 0 - score 1)).1)).comp hlink
    simpa only [Function.comp_apply] using hlog.comp_of_eq hgap rfl
  · have hgap : ContinuousAt (fun candidate : ScoreVector (Fin 3) =>
        candidate 0 - candidate 2) score :=
      (continuousAt_apply 0 score).sub (continuousAt_apply 2 score)
    have hlink : ContinuousAt (link : ℝ → ℝ) (score 0 - score 2) :=
      hcontinuous.continuousAt
    have hlog : ContinuousAt (fun value : ℝ => Real.log (link value)) (score 0 - score 2) := by
      simpa only [Function.comp_apply] using
        (Real.continuousAt_log
          (ne_of_gt (link.openProbability hstrict (score 0 - score 2)).1)).comp hlink
    simpa only [Function.comp_apply] using hlog.comp_of_eq hgap rfl

/-- The perturbed `a`-win frequency is uniformly below the source's `100/101` bound. -/
private theorem supplementETheorem5_a_win_frequency_le
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    ((5 * denominator + 1 : ℕ) : ℝ) /
        (((5 * denominator + 1 : ℕ) : ℝ) + ((5 * denominator : ℕ) : ℝ)) ≤
      (100 : ℝ) / 101 := by
  have hdenominatorReal : 0 < (denominator : ℝ) := by
    exact_mod_cast hdenominator
  have hdenominator_one : (1 : ℝ) ≤ denominator := by
    exact_mod_cast (Nat.succ_le_iff.mpr hdenominator)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  apply (div_le_iff₀ (by positivity)).2
  field_simp
  norm_num
  nlinarith [hdenominator_one]

/-- A perfect-fit distance is no larger than a point whose link value bounds its frequency. -/
private theorem perfectFitDistance_le_of_link_eq_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ))
    (first second : Alternative) (bound frequency : ℝ)
    (hfrequency : link (dataset.perfectFitDistance link hcontinuous first second) = frequency)
    (hfrequency_le : frequency ≤ link bound) :
    dataset.perfectFitDistance link hcontinuous first second ≤ bound := by
  by_contra hnot
  have hbound_lt : bound < dataset.perfectFitDistance link hcontinuous first second :=
    lt_of_not_ge hnot
  have hlink_lt := hstrict hbound_lt
  rw [hfrequency] at hlink_lt
  exact (not_lt_of_ge hfrequency_le) hlink_lt

/-- Every positive directed empirical frequency in the unit-fraction family is at most `100/101`. -/
private theorem supplementETheorem5_empiricalFrequency_le
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (first second : Fin 3) (hdistinct : first ≠ second) :
    ((supplementETheorem5Dataset 1 denominator).count first second : ℝ) /
        (((supplementETheorem5Dataset 1 denominator).count first second : ℝ) +
          ((supplementETheorem5Dataset 1 denominator).count second first : ℝ)) ≤
      (100 : ℝ) / 101 := by
  have hdenominatorReal : 0 < (denominator : ℝ) := by
    exact_mod_cast hdenominator
  have hdenominator_one : (1 : ℝ) ≤ denominator := by
    exact_mod_cast (Nat.succ_le_iff.mpr hdenominator)
  fin_cases first <;> fin_cases second
  all_goals
    simp [supplementETheorem5Dataset] at hdistinct ⊢ <;>
      apply (div_le_iff₀ (by positivity)).2 <;>
      field_simp <;>
      norm_num <;>
      nlinarith [hdenominator_one]

/-- Every off-diagonal count in the unit-fraction Supplement-E family is positive. -/
private theorem supplementETheorem5Dataset_complete
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    ∀ first second : Fin 3, first ≠ second →
      0 < (supplementETheorem5Dataset 1 denominator).count first second := by
  intro first second hdifferent
  fin_cases first <;> fin_cases second
  all_goals simp [supplementETheorem5Dataset] at hdifferent ⊢ <;> omega

/--
The source's `F⁻¹(100/101)` is a common positive upper bound for every
perfect-fit distance in the exact `ε = 1 / denominator` dataset family.
-/
private theorem supplementETheorem5_maxPerfectFitDistance_le
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) (bound : ℝ)
    (hbound : link bound = (100 : ℝ) / 101)
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    (supplementETheorem5Dataset 1 denominator).maxPerfectFitDistance link hcontinuous 2 ≤ bound := by
  classical
  have hzero : link 0 = (1 : ℝ) / 2 := by
    have hcomplementary := link.complementary 0
    norm_num at hcomplementary ⊢
    linarith
  have hboundPos : 0 < bound := by
    by_contra hnot
    have hbound_nonpos : bound ≤ 0 := le_of_not_gt hnot
    have hlink_le := link.monotone hbound_nonpos
    rw [hbound, hzero] at hlink_le
    norm_num at hlink_le
  have hboundNonneg : 0 ≤ bound := hboundPos.le
  simp only [maxPerfectFitDistance]
  refine Finset.max'_le _ _ bound ?_
  intro value hvalue
  obtain ⟨⟨first, second⟩, _, rfl⟩ := Finset.mem_image.mp hvalue
  by_cases hsame : first = second
  · subst second
    rw [perfectFitDistance_self]
    exact hboundNonneg
  · refine perfectFitDistance_le_of_link_eq_le
      (supplementETheorem5Dataset 1 denominator) link hcontinuous hstrict first second bound
      (((supplementETheorem5Dataset 1 denominator).count first second : ℝ) /
        (((supplementETheorem5Dataset 1 denominator).count first second : ℝ) +
          ((supplementETheorem5Dataset 1 denominator).count second first : ℝ))) ?_ ?_
    · exact link_perfectFitDistance_eq_empirical_frequency
        (supplementETheorem5Dataset 1 denominator) link hcontinuous first second
        (supplementETheorem5Dataset_complete hdenominator first second hsame)
        (supplementETheorem5Dataset_complete hdenominator second first (Ne.symm hsame))
    · rw [hbound]
      exact supplementETheorem5_empiricalFrequency_le hdenominator first second hsame

/--
There is one compact score cube containing every fixed-reference MLE in the
integral `ε = 1 / denominator` family.  This is the finite compactness input
for the source's continuity/Berge step, made explicit for the exact data.
-/
private theorem exists_supplementETheorem5_uniform_score_bound
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    ∃ bound : ℝ, 0 < bound ∧ link bound = (100 : ℝ) / 101 ∧
      ∀ {denominator : ℕ}, 0 < denominator →
        ∀ score : ScoreVector (Fin 3),
          isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2 score →
            ∀ alternative, |score alternative| ≤ 3 * bound := by
  have hprobability : (100 : ℝ) / 101 ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨bound, hbound⟩ := link.exists_eq_of_mem_Ioo hcontinuous hprobability
  have hzero : link 0 = (1 : ℝ) / 2 := by
    have hcomplementary := link.complementary 0
    norm_num at hcomplementary ⊢
    linarith
  have hboundPos : 0 < bound := by
    by_contra hnot
    have hbound_nonpos : bound ≤ 0 := le_of_not_gt hnot
    have hlink_le := link.monotone hbound_nonpos
    rw [hbound, hzero] at hlink_le
    norm_num at hlink_le
  refine ⟨bound, hboundPos, hbound, ?_⟩
  intro denominator hdenominator score hmle alternative
  have hnorm := scoreSupNorm_le_card_mul_maxPerfectFitDistance_of_pairwiseMLE
    (supplementETheorem5Dataset 1 denominator) link hcontinuous hstrict 2 score hmle
    (supplementETheorem5Dataset_complete hdenominator)
  have hmax := supplementETheorem5_maxPerfectFitDistance_le link hcontinuous hstrict bound
    hbound hdenominator
  have hnorm_le : scoreSupNorm 2 score ≤ 3 * bound := by
    norm_num at hnorm ⊢
    nlinarith
  exact (abs_score_le_scoreSupNorm 2 alternative score).trans hnorm_le

/-- Complete positive directed counts make every undirected component strongly connected. -/
private theorem everyComponentStronglyConnected_of_complete
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative)
    (hcomplete : ∀ first second, first ≠ second → 0 < dataset.count first second) :
    dataset.everyComponentStronglyConnected := by
  intro first second _
  unfold PairwiseCountDataset.reaches
  by_cases hEq : first = second
  · subst second
    rfl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (hcomplete first second hEq)

/-- Complete positive directed counts make the comparison graph connected. -/
private theorem isConnected_of_complete
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative)
    (hcomplete : ∀ first second, first ≠ second → 0 < dataset.count first second) :
    dataset.isConnected := by
  intro first second
  unfold PairwiseCountDataset.connectedTo
  by_cases hEq : first = second
  · subst second
    rfl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Or.inl (hcomplete first second hEq))

/-- The `ε = 0`, denominator-one Supplement-E dataset has all positive off-diagonal counts. -/
private theorem supplementETheorem5BaseDataset_complete :
    ∀ first second : Fin 3, first ≠ second →
      0 < (supplementETheorem5Dataset 0 1).count first second := by
  intro first second hdifferent
  fin_cases first <;> fin_cases second
  all_goals simp [supplementETheorem5Dataset] at hdifferent ⊢

/--
The score reflection used in Supplement E at `ε = 0`: it fixes `b,c` and
reflects `a` across their midpoint.  Under the source's normalization
`score(c) = 0`, this is exactly `score(a) ↦ score(b) - score(a)`.
-/
def supplementETheorem5BaseReflection (score : ScoreVector (Fin 3)) :
    ScoreVector (Fin 3) :=
  fun alternative => if alternative.val = 0 then score 1 + score 2 - score 0 else score alternative

/--
At the unperturbed source dataset, the Supplement-E reflection swaps the two
equal-weighted `a,b` and `a,c` comparison terms and leaves the `b,c` terms
unchanged.  Thus it preserves the finite likelihood for every link and every
score vector.
-/
theorem pairwiseLogLikelihood_supplementETheorem5BaseReflection
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3)) :
    pairwiseLogLikelihood (supplementETheorem5Dataset 0 denominator) link
        (supplementETheorem5BaseReflection score) =
      pairwiseLogLikelihood (supplementETheorem5Dataset 0 denominator) link score := by
  classical
  unfold pairwiseLogLikelihood
  rw [supplementETheorem5_offDiag]
  simp [supplementETheorem5Dataset]
  unfold randomUtilityWinProbability
  simp [supplementETheorem5BaseReflection]
  ring_nf

/--
At the base parameter `ε = 0`, a unique MLE normalized at `c` must put `a` at
the midpoint of `b,c`.  The source proves the same fact by strict concavity
after observing the reflected score vector has equal likelihood; uniqueness is
the resulting property required here.
-/
theorem supplementETheorem5Base_mle_midpoint_of_unique
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 other →
        other = score) :
    score 0 = (score 1 + score 2) / 2 := by
  have hreflectionNormalized :
      isReferenceNormalized 2 (supplementETheorem5BaseReflection score) := by
    simpa [isReferenceNormalized, supplementETheorem5BaseReflection] using hmle.1
  have hreflectionMax :
      IsMaxOn (pairwiseLogLikelihood (supplementETheorem5Dataset 0 denominator) link)
        {candidate : ScoreVector (Fin 3) | isReferenceNormalized 2 candidate}
        (supplementETheorem5BaseReflection score) := by
    intro candidate hcandidate
    rw [pairwiseLogLikelihood_supplementETheorem5BaseReflection]
    exact hmle.2 hcandidate
  have hreflectionMLE :
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2
        (supplementETheorem5BaseReflection score) :=
    ⟨hreflectionNormalized, hreflectionMax⟩
  have hreflectionEq := hunique _ hreflectionMLE
  have hzero := congrFun hreflectionEq 0
  simp [supplementETheorem5BaseReflection] at hzero
  linarith

/-- The source's one-dimensional `(α / 2, α, 0)` score family at `ε = 0`. -/
noncomputable def supplementETheorem5BaseLineScore (parameter : ℝ) : ScoreVector (Fin 3) :=
  fun alternative =>
    if alternative.val = 0 then parameter / 2 else
    if alternative.val = 1 then parameter else 0

/--
The exact unperturbed one-dimensional likelihood displayed in Supplement E,
including the common integer scaling factor used for rational frequencies.
-/
noncomputable def supplementETheorem5BaseLineLogLikelihood
    (denominator : ℕ) (link : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  10 * (denominator : ℝ) * Real.log (link (parameter / 2)) +
    10 * (denominator : ℝ) * Real.log (link (-parameter / 2)) +
      100 * (denominator : ℝ) * Real.log (link parameter) +
        (denominator : ℝ) * Real.log (link (-parameter))

/--
Restricting the finite source likelihood to `(α / 2, α, 0)` is exactly the
one-dimensional expression used in the Supplement-E derivative calculation.
-/
theorem pairwiseLogLikelihood_supplementETheorem5BaseLineScore
    (denominator : ℕ) (link : ℝ → ℝ) (parameter : ℝ) :
    pairwiseLogLikelihood (supplementETheorem5Dataset 0 denominator) link
        (supplementETheorem5BaseLineScore parameter) =
      supplementETheorem5BaseLineLogLikelihood denominator link parameter := by
  classical
  unfold pairwiseLogLikelihood
  rw [supplementETheorem5_offDiag]
  simp [supplementETheorem5Dataset]
  unfold randomUtilityWinProbability
  simp [supplementETheorem5BaseLineScore, supplementETheorem5BaseLineLogLikelihood]
  ring_nf

/--
The base MLE is the source's one-dimensional score vector once its fixed
reference is `c` and its MLE is unique.
-/
theorem supplementETheorem5Base_mle_eq_lineScore_of_unique
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 other →
        other = score) :
    score = supplementETheorem5BaseLineScore (score 1) := by
  have hmidpoint := supplementETheorem5Base_mle_midpoint_of_unique denominator link score
    hmle hunique
  have hreference : score 2 = 0 := hmle.1
  apply funext
  intro alternative
  fin_cases alternative
  · simp [supplementETheorem5BaseLineScore]
    linarith [hmidpoint, hreference]
  · simp [supplementETheorem5BaseLineScore]
  · simp [supplementETheorem5BaseLineScore]
    exact hreference

/--
The unique base MLE maximizes the exact one-dimensional Supplement-E
likelihood.  The remaining source derivative argument needs only to prove
that this one-dimensional maximizer has positive parameter.
-/
theorem supplementETheorem5BaseLineLogLikelihood_isMax_of_uniqueMLE
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 other →
        other = score) :
    ∀ parameter,
      supplementETheorem5BaseLineLogLikelihood denominator link parameter ≤
        supplementETheorem5BaseLineLogLikelihood denominator link (score 1) := by
  intro parameter
  have hlineNormalized :
      isReferenceNormalized 2 (supplementETheorem5BaseLineScore parameter) := by
    simp [isReferenceNormalized, supplementETheorem5BaseLineScore]
  have hmax := hmle.2 hlineNormalized
  have hscore := supplementETheorem5Base_mle_eq_lineScore_of_unique denominator link score
    hmle hunique
  rw [hscore, pairwiseLogLikelihood_supplementETheorem5BaseLineScore] at hmax
  simpa [pairwiseLogLikelihood_supplementETheorem5BaseLineScore] using hmax

/-- The unscaled one-dimensional Supplement-E likelihood written for an arbitrary `G`. -/
noncomputable def supplementETheorem5BaseScalarLikelihood
    (G : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  10 * G (parameter / 2) + 10 * G (-parameter / 2) +
    100 * G parameter + G (-parameter)

/-- The derivative expression displayed for the unscaled Supplement-E base likelihood. -/
noncomputable def supplementETheorem5BaseDerivative
    (derivative : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  5 * derivative (parameter / 2) - 5 * derivative (-parameter / 2) +
    100 * derivative parameter - derivative (-parameter)

/--
The exact chain-rule calculation for the one-dimensional expression printed in
Supplement E.
-/
theorem hasDerivAt_supplementETheorem5BaseScalarLikelihood
    (G derivative : ℝ → ℝ)
    (hderivative : ∀ point, HasDerivAt G (derivative point) point)
    (parameter : ℝ) :
    HasDerivAt (supplementETheorem5BaseScalarLikelihood G)
      (supplementETheorem5BaseDerivative derivative parameter) parameter := by
  have hhalf := (hderivative (parameter / 2)).comp parameter
    ((hasDerivAt_id parameter).div_const 2)
  have hnegHalf := (hderivative (-parameter / 2)).comp parameter
    (((hasDerivAt_id parameter).neg).div_const 2)
  have hself := (hderivative parameter).comp parameter (hasDerivAt_id parameter)
  have hneg := (hderivative (-parameter)).comp parameter (hasDerivAt_id parameter).neg
  have hsum := (((hhalf.const_mul 10).add (hnegHalf.const_mul 10)).add
    (hself.const_mul 100)).add hneg
  convert hsum using 1
  simp [supplementETheorem5BaseDerivative]
  ring

/-- The scaled finite-count base likelihood is the source scalar expression times its denominator. -/
theorem supplementETheorem5BaseLineLogLikelihood_eq_scale_scalar
    (denominator : ℕ) (link : ℝ → ℝ) (parameter : ℝ) :
    supplementETheorem5BaseLineLogLikelihood denominator link parameter =
      (denominator : ℝ) *
        supplementETheorem5BaseScalarLikelihood (fun point => Real.log (link point)) parameter := by
  unfold supplementETheorem5BaseLineLogLikelihood supplementETheorem5BaseScalarLikelihood
  ring

/--
The derivative of the exact scaled finite-count base likelihood is the scaled
Supplement-E derivative expression.
-/
theorem hasDerivAt_supplementETheorem5BaseLineLogLikelihood
    (denominator : ℕ) (link derivative : ℝ → ℝ)
    (hderivative : ∀ point,
      HasDerivAt (fun value => Real.log (link value)) (derivative point) point)
    (parameter : ℝ) :
    HasDerivAt (supplementETheorem5BaseLineLogLikelihood denominator link)
      ((denominator : ℝ) * supplementETheorem5BaseDerivative derivative parameter) parameter := by
  have hscalar := hasDerivAt_supplementETheorem5BaseScalarLikelihood
    (fun value => Real.log (link value)) derivative hderivative parameter
  have hfunction : supplementETheorem5BaseLineLogLikelihood denominator link =
      fun value => (denominator : ℝ) *
        supplementETheorem5BaseScalarLikelihood (fun point => Real.log (link point)) value := by
    funext value
    exact supplementETheorem5BaseLineLogLikelihood_eq_scale_scalar denominator link value
  rw [hfunction]
  simpa using hscalar.const_mul (denominator : ℝ)

/--
The scalar order calculation in Supplement E: if `G'` is antitone and
positive, then at every nonpositive parameter the displayed likelihood
derivative is at least `99 * G'(parameter)`.
-/
theorem supplementETheorem5BaseDerivative_lower_bound_of_antitone
    (derivative : ℝ → ℝ) (hantitone : Antitone derivative)
    {parameter : ℝ} (hparameter : parameter ≤ 0) :
    99 * derivative parameter ≤
      supplementETheorem5BaseDerivative derivative parameter := by
  have hhalf : parameter / 2 ≤ -parameter / 2 := by linarith
  have hwhole : parameter ≤ -parameter := by linarith
  have hhalfOrder : derivative (-parameter / 2) ≤ derivative (parameter / 2) :=
    hantitone hhalf
  have hwholeOrder : derivative (-parameter) ≤ derivative parameter :=
    hantitone hwhole
  unfold supplementETheorem5BaseDerivative
  linarith

/--
Consequently, the source derivative expression is strictly positive at every
nonpositive parameter when the derivative of `G = log ∘ F` is positive.
-/
theorem supplementETheorem5BaseDerivative_pos_of_antitone_of_pos
    (derivative : ℝ → ℝ) (hantitone : Antitone derivative)
    (hpositive : ∀ parameter, 0 < derivative parameter)
    {parameter : ℝ} (hparameter : parameter ≤ 0) :
    0 < supplementETheorem5BaseDerivative derivative parameter := by
  have hlower := supplementETheorem5BaseDerivative_lower_bound_of_antitone
    derivative hantitone hparameter
  have hpositive99 : 0 < 99 * derivative parameter := by
    nlinarith [hpositive parameter]
  linarith

/--
The calculus conclusion used at the end of the Supplement-E base argument:
a global maximizer whose derivative is strictly positive at every nonpositive
point must itself be positive.
-/
theorem parameter_pos_of_global_max_of_hasDerivAt_of_pos_on_nonpos
    (objective derivative : ℝ → ℝ) (parameter : ℝ)
    (hmax : ∀ other, objective other ≤ objective parameter)
    (hderivative : HasDerivAt objective (derivative parameter) parameter)
    (hpositive : ∀ other, other ≤ 0 → 0 < derivative other) :
    0 < parameter := by
  by_contra hnot
  have hparameter : parameter ≤ 0 := le_of_not_gt hnot
  have hlocal : IsLocalMax objective parameter := by
    filter_upwards with other
    exact hmax other
  have hzero : derivative parameter = 0 := hlocal.hasDerivAt_eq_zero hderivative
  linarith [hpositive parameter hparameter]

/--
Conditional closeout of the base-parameter sign argument in Supplement E.
The derivative formula is kept explicit because deriving it from `G = log ∘ F`
requires the source differentiability bridge for the CDF-like link.
-/
theorem supplementETheorem5Base_parameter_pos_of_derivative
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : ℝ → ℝ) (derivative : ℝ → ℝ)
    (hantitone : Antitone derivative) (hpositive : ∀ parameter, 0 < derivative parameter)
    (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 other →
        other = score)
    (hderivative :
      HasDerivAt (supplementETheorem5BaseLineLogLikelihood denominator link)
        ((denominator : ℝ) * supplementETheorem5BaseDerivative derivative (score 1))
        (score 1)) :
    0 < score 1 := by
  refine parameter_pos_of_global_max_of_hasDerivAt_of_pos_on_nonpos
    (supplementETheorem5BaseLineLogLikelihood denominator link)
    (fun parameter => (denominator : ℝ) *
      supplementETheorem5BaseDerivative derivative parameter)
    (score 1) ?_ ?_ ?_
  · exact supplementETheorem5BaseLineLogLikelihood_isMax_of_uniqueMLE denominator link score
      hmle hunique
  · exact hderivative
  · intro parameter hparameter
    have hbasePositive := supplementETheorem5BaseDerivative_pos_of_antitone_of_pos
      derivative hantitone hpositive hparameter
    have hdenominatorReal : 0 < (denominator : ℝ) := by
      exact_mod_cast hdenominator
    exact mul_pos hdenominatorReal hbasePositive

/--
With the explicit Supplement-E derivative bridge, the base MLE has the source
order `b > a > c`.  This is still proof support, not Theorem 5.3: the
parameter-continuity argument needed to move from `ε = 0` to `ε > 0` remains
separate.
-/
theorem supplementETheorem5Base_mle_orders_b_a_c_of_derivative
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : ℝ → ℝ) (derivative : ℝ → ℝ)
    (hantitone : Antitone derivative) (hpositive : ∀ parameter, 0 < derivative parameter)
    (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 other →
        other = score)
    (hderivative :
      HasDerivAt (supplementETheorem5BaseLineLogLikelihood denominator link)
        ((denominator : ℝ) * supplementETheorem5BaseDerivative derivative (score 1))
        (score 1)) :
    score 2 < score 0 ∧ score 0 < score 1 := by
  have hparameter := supplementETheorem5Base_parameter_pos_of_derivative hdenominator
    link derivative hantitone hpositive score hmle hunique hderivative
  have hmidpoint := supplementETheorem5Base_mle_midpoint_of_unique denominator link score
    hmle hunique
  have hreference : score 2 = 0 := hmle.1
  constructor <;> linarith

/--
The unperturbed Supplement-E MLE has the source order `b > a > c` under the
actual hypotheses of Theorem 5.3.  In particular, the positivity of the
derivative of `log ∘ F` is derived from strict monotonicity, strict
log-concavity, and differentiability; it is not an extra assumption.
-/
theorem supplementETheorem5Base_mle_orders_b_a_c
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ))
    (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 denominator) link 2 other →
        other = score) :
    score 2 < score 0 ∧ score 0 < score 1 := by
  let derivative : ℝ → ℝ := fun point => deriv (fun value : ℝ => Real.log (link value)) point
  have hlogDifferentiable : Differentiable ℝ (fun value : ℝ => Real.log (link value)) :=
    differentiable_log_comp_of_differentiable link hstrict hdifferentiable
  have hstrictAnti : StrictAntiOn derivative Set.univ := by
    exact hlogStrict.strictAntiOn_deriv (fun point _ => hlogDifferentiable point)
  have hantitone : Antitone derivative := by
    intro first second hfirstSecond
    by_cases hEq : first = second
    · subst second
      exact le_rfl
    · exact (hstrictAnti (by simp) (by simp)
        (lt_of_le_of_ne hfirstSecond hEq)).le
  have hpositive : ∀ point, 0 < derivative point := by
    intro point
    exact deriv_log_comp_pos_of_strictMono_strictConcave_differentiable
      link hstrict hlogStrict hdifferentiable point
  have hderivative :
      HasDerivAt (supplementETheorem5BaseLineLogLikelihood denominator link)
        ((denominator : ℝ) * supplementETheorem5BaseDerivative derivative (score 1))
        (score 1) := by
    apply hasDerivAt_supplementETheorem5BaseLineLogLikelihood denominator link derivative
    intro point
    exact (hlogDifferentiable point).hasDerivAt
  exact supplementETheorem5Base_mle_orders_b_a_c_of_derivative hdenominator
    link derivative hantitone hpositive score hmle hunique hderivative

/--
The finite compact-gap form of the final Supplement-E perturbation argument.
It uses the exact integral data with `ε = 1 / denominator`: a unique base
maximizer with `b > a`, a common compact score cube, and the displayed
linear-in-count likelihood identity force some positive denominator's MLE to
retain `b > a`.  This is a direct finite substitute for the source's appeal
to Berge's maximum theorem.
-/
private theorem supplementETheorem5_exists_unitFraction_mle_order_of_compact
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (baseScore : ScoreVector (Fin 3))
    (hbase : isPairwiseMLE (supplementETheorem5Dataset 0 1) link 2 baseScore)
    (hbaseUnique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 1) link 2 other → other = baseScore)
    (hbaseOrder : baseScore 0 < baseScore 1)
    (cubeBound : ℝ) (hcubeBound : 0 ≤ cubeBound)
    (hbaseCube : ∀ alternative, |baseScore alternative| ≤ cubeBound)
    (hmleExists : ∀ denominator : ℕ, 0 < denominator →
      ∃ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2 score)
    (hmleCube : ∀ {denominator : ℕ}, 0 < denominator →
      ∀ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2 score →
          ∀ alternative, |score alternative| ≤ cubeBound) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∃ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2 score ∧
          score 0 < score 1 := by
  let cube : Set (ScoreVector (Fin 3)) :=
    Set.univ.pi (fun _ : Fin 3 => Set.Icc (-cubeBound) cubeBound)
  let normalized : Set (ScoreVector (Fin 3)) :=
    cube ∩ {score | isReferenceNormalized 2 score}
  let bad : Set (ScoreVector (Fin 3)) := normalized ∩ {score | score 1 ≤ score 0}
  have hcubeCompact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Fin 3 => isCompact_Icc
  have hreferenceClosed : IsClosed {score : ScoreVector (Fin 3) |
      isReferenceNormalized 2 score} := by
    change IsClosed {score : ScoreVector (Fin 3) | score 2 = 0}
    exact isClosed_eq (continuous_apply 2) continuous_const
  have hnormalizedCompact : IsCompact normalized := by
    dsimp [normalized]
    exact hcubeCompact.inter_right hreferenceClosed
  have hbadOrderClosed : IsClosed {score : ScoreVector (Fin 3) | score 1 ≤ score 0} :=
    isClosed_le (continuous_apply 1) (continuous_apply 0)
  have hbadCompact : IsCompact bad := by
    dsimp [bad]
    exact hnormalizedCompact.inter_right hbadOrderClosed
  have hbaseInCube : baseScore ∈ cube := by
    intro alternative _
    exact ⟨(neg_le_neg (hbaseCube alternative)).trans (neg_abs_le _),
      (le_abs_self _).trans (hbaseCube alternative)⟩
  have hbaseInNormalized : baseScore ∈ normalized := ⟨hbaseInCube, hbase.1⟩
  have hbaseMax : IsMaxOn
      (pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link) normalized baseScore := by
    intro other hother
    exact hbase.2 hother.2
  have hbaseUniqueOn : ∀ other, other ∈ normalized →
      pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link other =
        pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link baseScore → other = baseScore := by
    intro other hother hvalue
    apply hbaseUnique other
    refine ⟨hother.2, ?_⟩
    intro candidate hcandidate
    calc
      pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link candidate ≤
          pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link baseScore :=
        hbase.2 hcandidate
      _ = pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link other := hvalue.symm
  have hbaseNotBad : baseScore ∉ bad := by
    intro hbaseBad
    exact (not_le_of_gt hbaseOrder) hbaseBad.2
  obtain ⟨denominator, hdenominator, score, hscoreInNormalized, _, hscore, hscoreNotBad⟩ :=
    exists_pos_nat_isMaxOn_scaled_add_not_mem_of_compact
      hnormalizedCompact hbadCompact (by intro score hscore; exact hscore.1)
      (continuous_pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link hcontinuous hstrict).continuousOn
      (continuous_supplementETheorem5Perturbation link hcontinuous hstrict).continuousOn
      ⟨hbaseInNormalized, hbaseMax⟩ hbaseUniqueOn hbaseNotBad (by
        intro denominator hdenominator
        obtain ⟨score, hscore⟩ := hmleExists denominator hdenominator
        have hscoreInCube : score ∈ cube := by
          intro alternative _
          have hscoreBound := hmleCube hdenominator score hscore alternative
          exact ⟨(neg_le_neg hscoreBound).trans (neg_abs_le _),
            (le_abs_self _).trans hscoreBound⟩
        have hscoreInNormalized : score ∈ normalized := ⟨hscoreInCube, hscore.1⟩
        refine ⟨score, hscoreInNormalized, ?_, hscore⟩
        intro candidate hcandidate
        change (denominator : ℝ) *
            pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link candidate +
              supplementETheorem5Perturbation link candidate ≤
          (denominator : ℝ) *
            pairwiseLogLikelihood (supplementETheorem5Dataset 0 1) link score +
              supplementETheorem5Perturbation link score
        rw [← pairwiseLogLikelihood_supplementETheorem5_unitFraction denominator link candidate,
          ← pairwiseLogLikelihood_supplementETheorem5_unitFraction denominator link score]
        exact hscore.2 hcandidate.2)
  refine ⟨denominator, hdenominator, score, hscore, ?_⟩
  by_contra hnotOrder
  exact hscoreNotBad ⟨hscoreInNormalized, le_of_not_gt hnotOrder⟩

/--
An exact finite Supplement-E witness with the source's reversed `b,a` MLE
order refutes the global Definition-5.1 pairwise-majority-consistency property.
-/
theorem supplementETheorem5_not_pairwiseMajorityConsistent_of_witness
    {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hnumerator_le : numerator ≤ denominator)
    (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementETheorem5Dataset numerator denominator) link 2 score)
    (horder : score 0 < score 1) :
    ¬ pairwiseMLEPairwiseMajorityConsistent.{0} link := by
  intro hconsistent
  have hmajority := supplementETheorem5Dataset_hasPairwiseMajorityRanking
    hnumerator hnumerator_le
  have hcontrary : score 1 ≤ score 0 := hconsistent
    (supplementETheorem5Dataset numerator denominator) 2 score supplementETheorem5Ranking
    hmle hmajority 0 1 (by decide)
  exact (not_le_of_gt horder) hcontrary

/--
Source Theorem 5.3.  Under the stated strict monotonicity, strict
log-concavity, and differentiability assumptions, the finite MLE rule fails
pairwise majority consistency.  The witness is the source's three-alternative
Supplement-E dataset for a sufficiently small positive rational
`ε = 1 / denominator`, realized exactly as integer counts.
-/
theorem theorem5_3_mle_violates_pairwise_majority_consistency_core
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ)) :
    ¬ pairwiseMLEPairwiseMajorityConsistent.{0} link := by
  have hcontinuous : Continuous (link : ℝ → ℝ) := hdifferentiable.continuous
  have hbaseStrong :
      (supplementETheorem5Dataset 0 1).everyComponentStronglyConnected :=
    everyComponentStronglyConnected_of_complete (supplementETheorem5Dataset 0 1)
      supplementETheorem5BaseDataset_complete
  obtain ⟨baseScore, hbase⟩ := exists_pairwiseMLE_of_everyComponentStronglyConnected
    (supplementETheorem5Dataset 0 1) link 2 hcontinuous hstrict hbaseStrong
  have hbaseConnected : (supplementETheorem5Dataset 0 1).isConnected :=
    isConnected_of_complete (supplementETheorem5Dataset 0 1)
      supplementETheorem5BaseDataset_complete
  have hbaseUnique : ∀ other,
      isPairwiseMLE (supplementETheorem5Dataset 0 1) link 2 other → other = baseScore := by
    intro other hother
    exact isPairwiseMLE_unique_of_isConnected (supplementETheorem5Dataset 0 1) link
      hlogStrict 2 hbaseConnected baseScore hbase other hother
  have hbaseOrder := supplementETheorem5Base_mle_orders_b_a_c
    (denominator := 1) (by omega) link hstrict hlogStrict hdifferentiable
    baseScore hbase hbaseUnique
  obtain ⟨uniformBound, huniformBoundPos, huniformBoundLink, huniformScoreBound⟩ :=
    exists_supplementETheorem5_uniform_score_bound link hcontinuous hstrict
  let cubeBound : ℝ := max (3 * uniformBound) (scoreSupNorm 2 baseScore)
  have hcubeBoundNonneg : 0 ≤ cubeBound := by
    dsimp [cubeBound]
    exact le_max_of_le_left (by positivity)
  have hbaseCube : ∀ alternative, |baseScore alternative| ≤ cubeBound := by
    intro alternative
    exact (abs_score_le_scoreSupNorm 2 alternative baseScore).trans
      (le_max_of_le_right le_rfl)
  have hmleExists : ∀ denominator : ℕ, 0 < denominator →
      ∃ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2 score := by
    intro denominator hdenominator
    apply exists_pairwiseMLE_of_everyComponentStronglyConnected
      (supplementETheorem5Dataset 1 denominator) link 2 hcontinuous hstrict
    exact everyComponentStronglyConnected_of_complete
      (supplementETheorem5Dataset 1 denominator)
      (supplementETheorem5Dataset_complete hdenominator)
  have hmleCube : ∀ {denominator : ℕ}, 0 < denominator →
      ∀ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2 score →
          ∀ alternative, |score alternative| ≤ cubeBound := by
    intro denominator hdenominator score hscore alternative
    exact (huniformScoreBound hdenominator score hscore alternative).trans
      (le_max_of_le_left le_rfl)
  obtain ⟨denominator, hdenominator, score, hscore, horder⟩ :=
    supplementETheorem5_exists_unitFraction_mle_order_of_compact
      link hcontinuous hstrict baseScore hbase hbaseUnique hbaseOrder.2
      cubeBound hcubeBoundNonneg hbaseCube hmleExists hmleCube
  exact supplementETheorem5_not_pairwiseMajorityConsistent_of_witness
    (by omega) (by omega) link score hscore horder

/--
Conditional finite closeout of Supplement E. Once the source's continuous MLE
path is supplied at the exact scaled datasets, its strict base order yields a
unit-fraction perturbation and hence a finite counterexample to Definition 5.1.
-/
theorem supplementETheorem5_not_pairwiseMajorityConsistent_of_continuousMLE_path
    (link : ℝ → ℝ) (scorePath : ℝ → ScoreVector (Fin 3))
    (hcontinuous : ContinuousAt
      (fun parameter => scorePath parameter 1 - scorePath parameter 0) 0)
    (hbaseOrder : scorePath 0 0 < scorePath 0 1)
    (hmlePath : ∀ denominator : ℕ, 0 < denominator →
      isPairwiseMLE (supplementETheorem5Dataset 1 denominator) link 2
        (scorePath ((1 : ℝ) / denominator)) ) :
    ¬ pairwiseMLEPairwiseMajorityConsistent.{0} link := by
  obtain ⟨denominator, hdenominator, hdenominator_one, horder⟩ :=
    exists_pos_unitFraction_score_order_of_continuousAt scorePath 0 1 hcontinuous hbaseOrder
  exact supplementETheorem5_not_pairwiseMajorityConsistent_of_witness
    (by omega) hdenominator_one link
    (scorePath ((1 : ℝ) / denominator)) (hmlePath denominator hdenominator) horder

/--
The first component dataset in Supplement F, after scaling the source
perturbation `ε = numerator / denominator` by `denominator`.
-/
def supplementFTheorem6FirstDataset (numerator denominator : ℕ) :
    PairwiseCountDataset (Fin 3) where
  count := fun winner loser =>
    if winner.val = 0 ∧ loser.val = 2 then 5 * denominator + numerator else
    if winner.val = 2 ∧ loser.val = 0 then 5 * denominator - numerator else
    if winner.val = 2 ∧ loser.val = 1 then 100 * denominator else
    if winner.val = 1 ∧ loser.val = 2 then denominator else 0
  diagonal_zero := by
    intro alternative
    fin_cases alternative <;> simp

/--
The second component dataset in Supplement F, under the same rational scaling.
-/
def supplementFTheorem6SecondDataset (numerator denominator : ℕ) :
    PairwiseCountDataset (Fin 3) where
  count := fun winner loser =>
    if winner.val = 0 ∧ loser.val = 2 then 5 * denominator + numerator else
    if winner.val = 2 ∧ loser.val = 0 then 5 * denominator - numerator else
    if winner.val = 1 ∧ loser.val = 0 then 100 * denominator else
    if winner.val = 0 ∧ loser.val = 1 then denominator else 0
  diagonal_zero := by
    intro alternative
    fin_cases alternative <;> simp

/-- The explicitly pooled Supplement-F dataset. -/
def supplementFTheorem6PooledDataset (numerator denominator : ℕ) :
    PairwiseCountDataset (Fin 3) where
  count := fun winner loser =>
    if winner.val = 2 ∧ loser.val = 1 then 100 * denominator else
    if winner.val = 1 ∧ loser.val = 2 then denominator else
    if winner.val = 1 ∧ loser.val = 0 then 100 * denominator else
    if winner.val = 0 ∧ loser.val = 1 then denominator else
    if winner.val = 0 ∧ loser.val = 2 then 10 * denominator + 2 * numerator else
    if winner.val = 2 ∧ loser.val = 0 then 10 * denominator - 2 * numerator else 0
  diagonal_zero := by
    intro alternative
    fin_cases alternative <;> simp

/--
The two signed `a,c` perturbation terms in the integral `ε = 1 / denominator`
Supplement-F pooled objective.
-/
noncomputable def supplementFTheorem6PooledPerturbation
    (link : ℝ → ℝ) (score : ScoreVector (Fin 3)) : ℝ :=
  2 * (Real.log (link (score 0 - score 2)) - Real.log (link (score 2 - score 0)))

/--
For the exact integral pooled family, the likelihood is `denominator` times
the `ε = 0` likelihood plus its two source perturbation terms.
-/
theorem pairwiseLogLikelihood_supplementFTheorem6Pooled_unitFraction
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : ℝ → ℝ) (score : ScoreVector (Fin 3)) :
    pairwiseLogLikelihood (supplementFTheorem6PooledDataset 1 denominator) link score =
      (denominator : ℝ) *
        pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link score +
          supplementFTheorem6PooledPerturbation link score := by
  classical
  have htwo_le : 2 ≤ 10 * denominator := by omega
  have hreverseCount : ((10 * denominator - 2 : ℕ) : ℝ) =
      10 * (denominator : ℝ) - 2 := by
    rw [Nat.cast_sub htwo_le]
    norm_num
  unfold pairwiseLogLikelihood
  rw [supplementETheorem5_offDiag]
  simp [supplementFTheorem6PooledDataset, supplementFTheorem6PooledPerturbation]
  unfold randomUtilityWinProbability
  rw [hreverseCount]
  ring

/-- The finite pooled perturbation term is continuous under the source link hypotheses. -/
theorem continuous_supplementFTheorem6PooledPerturbation
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    Continuous (supplementFTheorem6PooledPerturbation link) := by
  rw [continuous_iff_continuousAt]
  intro score
  unfold supplementFTheorem6PooledPerturbation
  apply ContinuousAt.const_mul
  apply ContinuousAt.sub
  · have hgap : ContinuousAt (fun candidate : ScoreVector (Fin 3) =>
        candidate 0 - candidate 2) score :=
      (continuousAt_apply 0 score).sub (continuousAt_apply 2 score)
    have hlink : ContinuousAt (link : ℝ → ℝ) (score 0 - score 2) :=
      hcontinuous.continuousAt
    have hlog : ContinuousAt (fun value : ℝ => Real.log (link value)) (score 0 - score 2) := by
      simpa only [Function.comp_apply] using
        (Real.continuousAt_log
          (ne_of_gt (link.openProbability hstrict (score 0 - score 2)).1)).comp hlink
    simpa only [Function.comp_apply] using hlog.comp_of_eq hgap rfl
  · have hgap : ContinuousAt (fun candidate : ScoreVector (Fin 3) =>
        candidate 2 - candidate 0) score :=
      (continuousAt_apply 2 score).sub (continuousAt_apply 0 score)
    have hlink : ContinuousAt (link : ℝ → ℝ) (score 2 - score 0) :=
      hcontinuous.continuousAt
    have hlog : ContinuousAt (fun value : ℝ => Real.log (link value)) (score 2 - score 0) := by
      simpa only [Function.comp_apply] using
        (Real.continuousAt_log
          (ne_of_gt (link.openProbability hstrict (score 2 - score 0)).1)).comp hlink
    simpa only [Function.comp_apply] using hlog.comp_of_eq hgap rfl

/-- Every positive pooled empirical frequency in the unit-fraction family is at most `100/101`. -/
private theorem supplementFTheorem6Pooled_empiricalFrequency_le
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (first second : Fin 3) (hdistinct : first ≠ second) :
    ((supplementFTheorem6PooledDataset 1 denominator).count first second : ℝ) /
        (((supplementFTheorem6PooledDataset 1 denominator).count first second : ℝ) +
          ((supplementFTheorem6PooledDataset 1 denominator).count second first : ℝ)) ≤
      (100 : ℝ) / 101 := by
  have hdenominatorReal : 0 < (denominator : ℝ) := by
    exact_mod_cast hdenominator
  have hdenominator_one : (1 : ℝ) ≤ denominator := by
    exact_mod_cast (Nat.succ_le_iff.mpr hdenominator)
  have htwo_le : 2 ≤ 10 * denominator := by omega
  have hreverseCount : ((10 * denominator - 2 : ℕ) : ℝ) =
      10 * (denominator : ℝ) - 2 := by
    rw [Nat.cast_sub htwo_le]
    norm_num
  fin_cases first <;> fin_cases second
  all_goals
    simp [supplementFTheorem6PooledDataset, hreverseCount] at hdistinct ⊢ <;>
      apply (div_le_iff₀ (by positivity)).2 <;>
      field_simp <;>
      norm_num <;>
      nlinarith [hdenominator_one]

/-- Every off-diagonal pooled count is positive in the unit-fraction family. -/
private theorem supplementFTheorem6PooledDataset_complete
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    ∀ first second : Fin 3, first ≠ second →
      0 < (supplementFTheorem6PooledDataset 1 denominator).count first second := by
  intro first second hdifferent
  fin_cases first <;> fin_cases second
  all_goals simp [supplementFTheorem6PooledDataset] at hdifferent ⊢ <;> omega

/-- The source's `F⁻¹(100/101)` bounds all pooled perfect-fit distances in the unit-fraction family. -/
private theorem supplementFTheorem6Pooled_maxPerfectFitDistance_le
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) (bound : ℝ)
    (hbound : link bound = (100 : ℝ) / 101)
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    (supplementFTheorem6PooledDataset 1 denominator).maxPerfectFitDistance link hcontinuous 0 ≤ bound := by
  classical
  have hzero : link 0 = (1 : ℝ) / 2 := by
    have hcomplementary := link.complementary 0
    norm_num at hcomplementary ⊢
    linarith
  have hboundPos : 0 < bound := by
    by_contra hnot
    have hbound_nonpos : bound ≤ 0 := le_of_not_gt hnot
    have hlink_le := link.monotone hbound_nonpos
    rw [hbound, hzero] at hlink_le
    norm_num at hlink_le
  have hboundNonneg : 0 ≤ bound := hboundPos.le
  unfold maxPerfectFitDistance
  refine Finset.max'_le _ _ bound ?_
  intro value hvalue
  obtain ⟨⟨first, second⟩, _, rfl⟩ := Finset.mem_image.mp hvalue
  by_cases hsame : first = second
  · subst second
    rw [perfectFitDistance_self]
    exact hboundNonneg
  · refine perfectFitDistance_le_of_link_eq_le
      (supplementFTheorem6PooledDataset 1 denominator) link hcontinuous hstrict first second bound
      (((supplementFTheorem6PooledDataset 1 denominator).count first second : ℝ) /
        (((supplementFTheorem6PooledDataset 1 denominator).count first second : ℝ) +
          ((supplementFTheorem6PooledDataset 1 denominator).count second first : ℝ))) ?_ ?_
    · exact link_perfectFitDistance_eq_empirical_frequency
        (supplementFTheorem6PooledDataset 1 denominator) link hcontinuous first second
        (supplementFTheorem6PooledDataset_complete hdenominator first second hsame)
        (supplementFTheorem6PooledDataset_complete hdenominator second first (Ne.symm hsame))
    · rw [hbound]
      exact supplementFTheorem6Pooled_empiricalFrequency_le hdenominator first second hsame

/-- One compact score cube contains every fixed-reference pooled MLE in the unit-fraction family. -/
private theorem exists_supplementFTheorem6Pooled_uniform_score_bound
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    ∃ bound : ℝ, 0 < bound ∧ link bound = (100 : ℝ) / 101 ∧
      ∀ {denominator : ℕ}, 0 < denominator →
        ∀ score : ScoreVector (Fin 3),
          isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0 score →
            ∀ alternative, |score alternative| ≤ 3 * bound := by
  have hprobability : (100 : ℝ) / 101 ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨bound, hbound⟩ := link.exists_eq_of_mem_Ioo hcontinuous hprobability
  have hzero : link 0 = (1 : ℝ) / 2 := by
    have hcomplementary := link.complementary 0
    norm_num at hcomplementary ⊢
    linarith
  have hboundPos : 0 < bound := by
    by_contra hnot
    have hbound_nonpos : bound ≤ 0 := le_of_not_gt hnot
    have hlink_le := link.monotone hbound_nonpos
    rw [hbound, hzero] at hlink_le
    norm_num at hlink_le
  refine ⟨bound, hboundPos, hbound, ?_⟩
  intro denominator hdenominator score hmle alternative
  have hnorm := scoreSupNorm_le_card_mul_maxPerfectFitDistance_of_pairwiseMLE
    (supplementFTheorem6PooledDataset 1 denominator) link hcontinuous hstrict 0 score hmle
    (supplementFTheorem6PooledDataset_complete hdenominator)
  have hmax := supplementFTheorem6Pooled_maxPerfectFitDistance_le link hcontinuous hstrict bound
    hbound hdenominator
  have hnorm_le : scoreSupNorm 0 score ≤ 3 * bound := by
    norm_num at hnorm ⊢
    nlinarith
  exact (abs_score_le_scoreSupNorm 0 alternative score).trans hnorm_le

/-- The unperturbed pooled Supplement-F dataset has all positive off-diagonal counts. -/
private theorem supplementFTheorem6PooledBaseDataset_complete :
    ∀ first second : Fin 3, first ≠ second →
      0 < (supplementFTheorem6PooledDataset 0 1).count first second := by
  intro first second hdifferent
  fin_cases first <;> fin_cases second
  all_goals simp [supplementFTheorem6PooledDataset] at hdifferent ⊢

/--
The score reflection used in Supplement F at `ε = 0`: it fixes `a,c` and
reflects `b` across their midpoint.  Under the source's normalization
`score(a) = 0`, this is `score(b) ↦ score(c) - score(b)`.
-/
def supplementFTheorem6PooledBaseReflection (score : ScoreVector (Fin 3)) :
    ScoreVector (Fin 3) :=
  fun alternative =>
    if alternative.val = 1 then score 2 + score 0 - score 1 else score alternative

/--
At the unperturbed pooled source dataset, the Supplement-F reflection swaps
the equal-weighted `c,b` and `b,a` terms and leaves the `a,c` terms unchanged.
Thus it preserves the finite likelihood for every link and score vector.
-/
theorem pairwiseLogLikelihood_supplementFTheorem6PooledBaseReflection
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3)) :
    pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 denominator) link
        (supplementFTheorem6PooledBaseReflection score) =
      pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 denominator) link score := by
  classical
  unfold pairwiseLogLikelihood
  rw [supplementETheorem5_offDiag]
  simp [supplementFTheorem6PooledDataset]
  unfold randomUtilityWinProbability
  simp [supplementFTheorem6PooledBaseReflection]
  ring_nf

/--
At the base parameter `ε = 0`, a unique pooled MLE normalized at `a` puts `b`
at the midpoint of `a,c`.  This is the source symmetry conclusion; strict
concavity is used in the source to derive the required uniqueness.
-/
theorem supplementFTheorem6PooledBase_mle_midpoint_of_unique
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 other →
        other = score) :
    score 1 = (score 2 + score 0) / 2 := by
  have hreflectionNormalized :
      isReferenceNormalized 0 (supplementFTheorem6PooledBaseReflection score) := by
    simpa [isReferenceNormalized, supplementFTheorem6PooledBaseReflection] using hmle.1
  have hreflectionMax :
      IsMaxOn (pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 denominator) link)
        {candidate : ScoreVector (Fin 3) | isReferenceNormalized 0 candidate}
        (supplementFTheorem6PooledBaseReflection score) := by
    intro candidate hcandidate
    rw [pairwiseLogLikelihood_supplementFTheorem6PooledBaseReflection]
    exact hmle.2 hcandidate
  have hreflectionMLE :
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0
        (supplementFTheorem6PooledBaseReflection score) :=
    ⟨hreflectionNormalized, hreflectionMax⟩
  have hreflectionEq := hunique _ hreflectionMLE
  have hmiddle := congrFun hreflectionEq 1
  simp [supplementFTheorem6PooledBaseReflection] at hmiddle
  linarith

/-- The source's one-dimensional `(0, α / 2, α)` pooled score family at `ε = 0`. -/
noncomputable def supplementFTheorem6PooledBaseLineScore (parameter : ℝ) :
    ScoreVector (Fin 3) :=
  fun alternative =>
    if alternative.val = 1 then parameter / 2 else
    if alternative.val = 2 then parameter else 0

/--
The exact unperturbed one-dimensional pooled likelihood displayed in
Supplement F, including the common integer scaling used for rational
frequencies.
-/
noncomputable def supplementFTheorem6PooledBaseLineLogLikelihood
    (denominator : ℕ) (link : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  200 * (denominator : ℝ) * Real.log (link (parameter / 2)) +
    2 * (denominator : ℝ) * Real.log (link (-parameter / 2)) +
      10 * (denominator : ℝ) * Real.log (link parameter) +
        10 * (denominator : ℝ) * Real.log (link (-parameter))

/--
Restricting the finite pooled source likelihood to `(0, α / 2, α)` is exactly
the one-dimensional expression used in the Supplement-F derivative argument.
-/
theorem pairwiseLogLikelihood_supplementFTheorem6PooledBaseLineScore
    (denominator : ℕ) (link : ℝ → ℝ) (parameter : ℝ) :
    pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 denominator) link
        (supplementFTheorem6PooledBaseLineScore parameter) =
      supplementFTheorem6PooledBaseLineLogLikelihood denominator link parameter := by
  classical
  unfold pairwiseLogLikelihood
  rw [supplementETheorem5_offDiag]
  simp [supplementFTheorem6PooledDataset]
  unfold randomUtilityWinProbability
  simp [supplementFTheorem6PooledBaseLineScore,
    supplementFTheorem6PooledBaseLineLogLikelihood]
  ring_nf

/--
The unique pooled base MLE is the source's one-dimensional score vector once
the reference alternative is `a`.
-/
theorem supplementFTheorem6PooledBase_mle_eq_lineScore_of_unique
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 other →
        other = score) :
    score = supplementFTheorem6PooledBaseLineScore (score 2) := by
  have hmidpoint := supplementFTheorem6PooledBase_mle_midpoint_of_unique denominator link score
    hmle hunique
  have hreference : score 0 = 0 := hmle.1
  apply funext
  intro alternative
  fin_cases alternative
  · simp [supplementFTheorem6PooledBaseLineScore]
    exact hreference
  · simp [supplementFTheorem6PooledBaseLineScore]
    linarith [hmidpoint, hreference]
  · simp [supplementFTheorem6PooledBaseLineScore]

/-- The unique pooled base MLE maximizes the exact one-dimensional likelihood. -/
theorem supplementFTheorem6PooledBaseLineLogLikelihood_isMax_of_uniqueMLE
    (denominator : ℕ) (link : ℝ → ℝ) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 other →
        other = score) :
    ∀ parameter,
      supplementFTheorem6PooledBaseLineLogLikelihood denominator link parameter ≤
        supplementFTheorem6PooledBaseLineLogLikelihood denominator link (score 2) := by
  intro parameter
  have hlineNormalized :
      isReferenceNormalized 0 (supplementFTheorem6PooledBaseLineScore parameter) := by
    simp [isReferenceNormalized, supplementFTheorem6PooledBaseLineScore]
  have hmax := hmle.2 hlineNormalized
  have hscore := supplementFTheorem6PooledBase_mle_eq_lineScore_of_unique denominator link score
    hmle hunique
  rw [hscore, pairwiseLogLikelihood_supplementFTheorem6PooledBaseLineScore] at hmax
  simpa [pairwiseLogLikelihood_supplementFTheorem6PooledBaseLineScore] using hmax

/-- The unscaled one-dimensional Supplement-F pooled likelihood for an arbitrary `G`. -/
noncomputable def supplementFTheorem6PooledBaseScalarLikelihood
    (G : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  200 * G (parameter / 2) + 2 * G (-parameter / 2) +
    10 * G parameter + 10 * G (-parameter)

/-- The derivative expression displayed for the unscaled Supplement-F pooled likelihood. -/
noncomputable def supplementFTheorem6PooledBaseDerivative
    (derivative : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  100 * derivative (parameter / 2) - derivative (-parameter / 2) +
    10 * derivative parameter - 10 * derivative (-parameter)

/-- The exact chain-rule calculation for the one-dimensional expression in Supplement F. -/
theorem hasDerivAt_supplementFTheorem6PooledBaseScalarLikelihood
    (G derivative : ℝ → ℝ)
    (hderivative : ∀ point, HasDerivAt G (derivative point) point)
    (parameter : ℝ) :
    HasDerivAt (supplementFTheorem6PooledBaseScalarLikelihood G)
      (supplementFTheorem6PooledBaseDerivative derivative parameter) parameter := by
  have hhalf := (hderivative (parameter / 2)).comp parameter
    ((hasDerivAt_id parameter).div_const 2)
  have hnegHalf := (hderivative (-parameter / 2)).comp parameter
    (((hasDerivAt_id parameter).neg).div_const 2)
  have hself := (hderivative parameter).comp parameter (hasDerivAt_id parameter)
  have hneg := (hderivative (-parameter)).comp parameter (hasDerivAt_id parameter).neg
  have hsum := (((hhalf.const_mul 200).add (hnegHalf.const_mul 2)).add
    (hself.const_mul 10)).add (hneg.const_mul 10)
  convert hsum using 1
  simp [supplementFTheorem6PooledBaseDerivative]
  ring

/-- The scaled finite-count pooled likelihood is the source scalar expression times its denominator. -/
theorem supplementFTheorem6PooledBaseLineLogLikelihood_eq_scale_scalar
    (denominator : ℕ) (link : ℝ → ℝ) (parameter : ℝ) :
    supplementFTheorem6PooledBaseLineLogLikelihood denominator link parameter =
      (denominator : ℝ) *
        supplementFTheorem6PooledBaseScalarLikelihood (fun point => Real.log (link point)) parameter := by
  unfold supplementFTheorem6PooledBaseLineLogLikelihood
    supplementFTheorem6PooledBaseScalarLikelihood
  ring

/--
The derivative of the exact scaled pooled base likelihood is the scaled
Supplement-F derivative expression.
-/
theorem hasDerivAt_supplementFTheorem6PooledBaseLineLogLikelihood
    (denominator : ℕ) (link derivative : ℝ → ℝ)
    (hderivative : ∀ point,
      HasDerivAt (fun value => Real.log (link value)) (derivative point) point)
    (parameter : ℝ) :
    HasDerivAt (supplementFTheorem6PooledBaseLineLogLikelihood denominator link)
      ((denominator : ℝ) * supplementFTheorem6PooledBaseDerivative derivative parameter) parameter := by
  have hscalar := hasDerivAt_supplementFTheorem6PooledBaseScalarLikelihood
    (fun value => Real.log (link value)) derivative hderivative parameter
  have hfunction : supplementFTheorem6PooledBaseLineLogLikelihood denominator link =
      fun value => (denominator : ℝ) *
        supplementFTheorem6PooledBaseScalarLikelihood (fun point => Real.log (link point)) value := by
    funext value
    exact supplementFTheorem6PooledBaseLineLogLikelihood_eq_scale_scalar denominator link value
  rw [hfunction]
  simpa using hscalar.const_mul (denominator : ℝ)

/--
The scalar order calculation in Supplement F: at a nonpositive parameter, an
antitone derivative makes the displayed derivative at least
`99 * G'(parameter / 2)`.
-/
theorem supplementFTheorem6PooledBaseDerivative_lower_bound_of_antitone
    (derivative : ℝ → ℝ) (hantitone : Antitone derivative)
    {parameter : ℝ} (hparameter : parameter ≤ 0) :
    99 * derivative (parameter / 2) ≤
      supplementFTheorem6PooledBaseDerivative derivative parameter := by
  have hhalf : parameter / 2 ≤ -parameter / 2 := by linarith
  have hwhole : parameter ≤ -parameter := by linarith
  have hhalfOrder : derivative (-parameter / 2) ≤ derivative (parameter / 2) :=
    hantitone hhalf
  have hwholeOrder : derivative (-parameter) ≤ derivative parameter :=
    hantitone hwhole
  unfold supplementFTheorem6PooledBaseDerivative
  linarith

/-- The Supplement-F source derivative is positive at every nonpositive point. -/
theorem supplementFTheorem6PooledBaseDerivative_pos_of_antitone_of_pos
    (derivative : ℝ → ℝ) (hantitone : Antitone derivative)
    (hpositive : ∀ parameter, 0 < derivative parameter)
    {parameter : ℝ} (hparameter : parameter ≤ 0) :
    0 < supplementFTheorem6PooledBaseDerivative derivative parameter := by
  have hlower := supplementFTheorem6PooledBaseDerivative_lower_bound_of_antitone
    derivative hantitone hparameter
  have hpositive99 : 0 < 99 * derivative (parameter / 2) := by
    nlinarith [hpositive (parameter / 2)]
  linarith

/--
Conditional closeout of Supplement F's pooled base-parameter sign argument.
The differentiability bridge from the source CDF-like link remains explicit.
-/
theorem supplementFTheorem6PooledBase_parameter_pos_of_derivative
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : ℝ → ℝ) (derivative : ℝ → ℝ)
    (hantitone : Antitone derivative) (hpositive : ∀ parameter, 0 < derivative parameter)
    (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 other →
        other = score)
    (hderivative :
      HasDerivAt (supplementFTheorem6PooledBaseLineLogLikelihood denominator link)
        ((denominator : ℝ) * supplementFTheorem6PooledBaseDerivative derivative (score 2))
        (score 2)) :
    0 < score 2 := by
  refine parameter_pos_of_global_max_of_hasDerivAt_of_pos_on_nonpos
    (supplementFTheorem6PooledBaseLineLogLikelihood denominator link)
    (fun parameter => (denominator : ℝ) *
      supplementFTheorem6PooledBaseDerivative derivative parameter)
    (score 2) ?_ ?_ ?_
  · exact supplementFTheorem6PooledBaseLineLogLikelihood_isMax_of_uniqueMLE denominator link score
      hmle hunique
  · exact hderivative
  · intro parameter hparameter
    have hbasePositive := supplementFTheorem6PooledBaseDerivative_pos_of_antitone_of_pos
      derivative hantitone hpositive hparameter
    have hdenominatorReal : 0 < (denominator : ℝ) := by
      exact_mod_cast hdenominator
    exact mul_pos hdenominatorReal hbasePositive

/--
With the explicit Supplement-F derivative bridge, the pooled base MLE has
the source order `c > b > a`. This is proof support, not Theorem 6.3: moving
from `ε = 0` to a positive rational perturbation still needs the source
continuity argument for the unique pooled MLE path.
-/
theorem supplementFTheorem6PooledBase_mle_orders_c_b_a_of_derivative
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : ℝ → ℝ) (derivative : ℝ → ℝ)
    (hantitone : Antitone derivative) (hpositive : ∀ parameter, 0 < derivative parameter)
    (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 other →
        other = score)
    (hderivative :
      HasDerivAt (supplementFTheorem6PooledBaseLineLogLikelihood denominator link)
        ((denominator : ℝ) * supplementFTheorem6PooledBaseDerivative derivative (score 2))
        (score 2)) :
    score 0 < score 1 ∧ score 1 < score 2 := by
  have hparameter := supplementFTheorem6PooledBase_parameter_pos_of_derivative hdenominator
    link derivative hantitone hpositive score hmle hunique hderivative
  have hmidpoint := supplementFTheorem6PooledBase_mle_midpoint_of_unique denominator link score
    hmle hunique
  have hreference : score 0 = 0 := hmle.1
  constructor <;> linarith

/--
The unperturbed Supplement-F pooled MLE has the source order `c > b > a`
under the actual hypotheses of Theorem 6.3.  As for Supplement E, derivative
positivity is derived rather than assumed.
-/
theorem supplementFTheorem6PooledBase_mle_orders_c_b_a
    {denominator : ℕ} (hdenominator : 0 < denominator)
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ))
    (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 score)
    (hunique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 denominator) link 0 other →
        other = score) :
    score 0 < score 1 ∧ score 1 < score 2 := by
  let derivative : ℝ → ℝ := fun point => deriv (fun value : ℝ => Real.log (link value)) point
  have hlogDifferentiable : Differentiable ℝ (fun value : ℝ => Real.log (link value)) :=
    differentiable_log_comp_of_differentiable link hstrict hdifferentiable
  have hstrictAnti : StrictAntiOn derivative Set.univ := by
    exact hlogStrict.strictAntiOn_deriv (fun point _ => hlogDifferentiable point)
  have hantitone : Antitone derivative := by
    intro first second hfirstSecond
    by_cases hEq : first = second
    · subst second
      exact le_rfl
    · exact (hstrictAnti (by simp) (by simp)
        (lt_of_le_of_ne hfirstSecond hEq)).le
  have hpositive : ∀ point, 0 < derivative point := by
    intro point
    exact deriv_log_comp_pos_of_strictMono_strictConcave_differentiable
      link hstrict hlogStrict hdifferentiable point
  have hderivative :
      HasDerivAt (supplementFTheorem6PooledBaseLineLogLikelihood denominator link)
        ((denominator : ℝ) * supplementFTheorem6PooledBaseDerivative derivative (score 2))
        (score 2) := by
    apply hasDerivAt_supplementFTheorem6PooledBaseLineLogLikelihood denominator link derivative
    intro point
    exact (hlogDifferentiable point).hasDerivAt
  exact supplementFTheorem6PooledBase_mle_orders_c_b_a_of_derivative hdenominator
    link derivative hantitone hpositive score hmle hunique hderivative

/--
Finite compact-gap form of the final Supplement-F pooled perturbation step.
It forces a positive integral `ε = 1 / denominator` pooled MLE to retain the
base order `c > a`, without a separate abstract Berge theorem.
-/
private theorem supplementFTheorem6_exists_unitFraction_pooled_mle_order_of_compact
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (baseScore : ScoreVector (Fin 3))
    (hbase : isPairwiseMLE (supplementFTheorem6PooledDataset 0 1) link 0 baseScore)
    (hbaseUnique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 1) link 0 other → other = baseScore)
    (hbaseOrder : baseScore 0 < baseScore 2)
    (cubeBound : ℝ) (hcubeBound : 0 ≤ cubeBound)
    (hbaseCube : ∀ alternative, |baseScore alternative| ≤ cubeBound)
    (hmleExists : ∀ denominator : ℕ, 0 < denominator →
      ∃ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0 score)
    (hmleCube : ∀ {denominator : ℕ}, 0 < denominator →
      ∀ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0 score →
          ∀ alternative, |score alternative| ≤ cubeBound) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∃ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0 score ∧
          score 0 < score 2 := by
  let cube : Set (ScoreVector (Fin 3)) :=
    Set.univ.pi (fun _ : Fin 3 => Set.Icc (-cubeBound) cubeBound)
  let normalized : Set (ScoreVector (Fin 3)) :=
    cube ∩ {score | isReferenceNormalized 0 score}
  let bad : Set (ScoreVector (Fin 3)) := normalized ∩ {score | score 2 ≤ score 0}
  have hcubeCompact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Fin 3 => isCompact_Icc
  have hreferenceClosed : IsClosed {score : ScoreVector (Fin 3) |
      isReferenceNormalized 0 score} := by
    change IsClosed {score : ScoreVector (Fin 3) | score 0 = 0}
    exact isClosed_eq (continuous_apply 0) continuous_const
  have hnormalizedCompact : IsCompact normalized := by
    dsimp [normalized]
    exact hcubeCompact.inter_right hreferenceClosed
  have hbadOrderClosed : IsClosed {score : ScoreVector (Fin 3) | score 2 ≤ score 0} :=
    isClosed_le (continuous_apply 2) (continuous_apply 0)
  have hbadCompact : IsCompact bad := by
    dsimp [bad]
    exact hnormalizedCompact.inter_right hbadOrderClosed
  have hbaseInCube : baseScore ∈ cube := by
    intro alternative _
    exact ⟨(neg_le_neg (hbaseCube alternative)).trans (neg_abs_le _),
      (le_abs_self _).trans (hbaseCube alternative)⟩
  have hbaseInNormalized : baseScore ∈ normalized := ⟨hbaseInCube, hbase.1⟩
  have hbaseMax : IsMaxOn
      (pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link) normalized baseScore := by
    intro other hother
    exact hbase.2 hother.2
  have hbaseUniqueOn : ∀ other, other ∈ normalized →
      pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link other =
        pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link baseScore → other = baseScore := by
    intro other hother hvalue
    apply hbaseUnique other
    refine ⟨hother.2, ?_⟩
    intro candidate hcandidate
    calc
      pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link candidate ≤
          pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link baseScore :=
        hbase.2 hcandidate
      _ = pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link other := hvalue.symm
  have hbaseNotBad : baseScore ∉ bad := by
    intro hbaseBad
    exact (not_le_of_gt hbaseOrder) hbaseBad.2
  obtain ⟨denominator, hdenominator, score, hscoreInNormalized, _, hscore, hscoreNotBad⟩ :=
    exists_pos_nat_isMaxOn_scaled_add_not_mem_of_compact
      hnormalizedCompact hbadCompact (by intro score hscore; exact hscore.1)
      (continuous_pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link hcontinuous hstrict).continuousOn
      (continuous_supplementFTheorem6PooledPerturbation link hcontinuous hstrict).continuousOn
      ⟨hbaseInNormalized, hbaseMax⟩ hbaseUniqueOn hbaseNotBad (by
        intro denominator hdenominator
        obtain ⟨score, hscore⟩ := hmleExists denominator hdenominator
        have hscoreInCube : score ∈ cube := by
          intro alternative _
          have hscoreBound := hmleCube hdenominator score hscore alternative
          exact ⟨(neg_le_neg hscoreBound).trans (neg_abs_le _),
            (le_abs_self _).trans hscoreBound⟩
        have hscoreInNormalized : score ∈ normalized := ⟨hscoreInCube, hscore.1⟩
        refine ⟨score, hscoreInNormalized, ?_, hscore⟩
        intro candidate hcandidate
        change (denominator : ℝ) *
            pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link candidate +
              supplementFTheorem6PooledPerturbation link candidate ≤
          (denominator : ℝ) *
            pairwiseLogLikelihood (supplementFTheorem6PooledDataset 0 1) link score +
              supplementFTheorem6PooledPerturbation link score
        rw [← pairwiseLogLikelihood_supplementFTheorem6Pooled_unitFraction hdenominator link candidate,
          ← pairwiseLogLikelihood_supplementFTheorem6Pooled_unitFraction hdenominator link score]
        exact hscore.2 hcandidate.2)
  refine ⟨denominator, hdenominator, score, hscore, ?_⟩
  by_contra hnotOrder
  exact hscoreNotBad ⟨hscoreInNormalized, le_of_not_gt hnotOrder⟩

/--
Pointwise pooling of the two Supplement-F component datasets is exactly the
source's displayed pooled count dataset.  The bound `numerator ≤ denominator`
is the source range `ε ∈ (0,1]` and ensures that natural-number subtraction
realizes the scaled reverse count.
-/
theorem supplementFTheorem6_first_add_second
    {numerator denominator : ℕ} (hnumerator_le : numerator ≤ denominator) :
    (supplementFTheorem6FirstDataset numerator denominator).add
        (supplementFTheorem6SecondDataset numerator denominator) =
      supplementFTheorem6PooledDataset numerator denominator := by
  apply PairwiseCountDataset.ext
  intro first second
  fin_cases first <;> fin_cases second <;>
    simp [supplementFTheorem6FirstDataset, supplementFTheorem6SecondDataset,
      supplementFTheorem6PooledDataset] <;>
    omega

/-- In the first Supplement-F component, `a` has only the neighbor `c`. -/
theorem supplementFTheorem6First_a_hasOnlyNeighbor_c
    (numerator denominator : ℕ) (hdenominator : 0 < denominator) :
    (supplementFTheorem6FirstDataset numerator denominator).hasOnlyNeighbor 0 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [supplementFTheorem6FirstDataset]
    omega
  · intro other hother_a hother_c
    fin_cases other <;> simp_all [supplementFTheorem6FirstDataset]

/-- In the first Supplement-F component, `b` has only the neighbor `c`. -/
theorem supplementFTheorem6First_b_hasOnlyNeighbor_c
    (numerator denominator : ℕ) (hdenominator : 0 < denominator) :
    (supplementFTheorem6FirstDataset numerator denominator).hasOnlyNeighbor 1 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [supplementFTheorem6FirstDataset]
    omega
  · intro other hother_b hother_c
    fin_cases other <;> simp_all [supplementFTheorem6FirstDataset]

/-- In the second Supplement-F component, `c` has only the neighbor `a`. -/
theorem supplementFTheorem6Second_c_hasOnlyNeighbor_a
    (numerator denominator : ℕ) (hdenominator : 0 < denominator) :
    (supplementFTheorem6SecondDataset numerator denominator).hasOnlyNeighbor 2 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [supplementFTheorem6SecondDataset]
    omega
  · intro other hother_c hother_a
    fin_cases other <;> simp_all [supplementFTheorem6SecondDataset]

/-- In the second Supplement-F component, `b` has only the neighbor `a`. -/
theorem supplementFTheorem6Second_b_hasOnlyNeighbor_a
    (numerator denominator : ℕ) (hdenominator : 0 < denominator) :
    (supplementFTheorem6SecondDataset numerator denominator).hasOnlyNeighbor 1 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [supplementFTheorem6SecondDataset]
    omega
  · intro other hother_b hother_a
    fin_cases other <;> simp_all [supplementFTheorem6SecondDataset]

/--
Every fixed-reference MLE of the first Supplement-F component satisfies the
source order `a > c > b`.
-/
theorem supplementFTheorem6First_mle_orders_a_c_b
    {numerator denominator : ℕ} (hnumerator : 0 < numerator)
    (hnumerator_le : numerator ≤ denominator)
    (link : CDFLikePairwiseLink) (reference : Fin 3) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6FirstDataset numerator denominator)
      link reference score)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ)) :
    score 1 < score 2 ∧ score 2 < score 0 := by
  have hdenominator : 0 < denominator := lt_of_lt_of_le hnumerator hnumerator_le
  constructor
  · apply isPairwiseMLE_score_lt_of_hasOnlyNeighbor_reverse_count_majority
      (supplementFTheorem6FirstDataset numerator denominator) link reference score hmle
      (supplementFTheorem6First_b_hasOnlyNeighbor_c numerator denominator hdenominator)
      (first := 1) (second := 2)
    all_goals norm_num [supplementFTheorem6FirstDataset]
    all_goals omega
  · apply isPairwiseMLE_score_lt_of_hasOnlyNeighbor_count_majority
      (supplementFTheorem6FirstDataset numerator denominator) link reference score hmle
      (supplementFTheorem6First_a_hasOnlyNeighbor_c numerator denominator hdenominator)
      (first := 0) (second := 2)
    all_goals norm_num [supplementFTheorem6FirstDataset]
    all_goals omega

/--
Every fixed-reference MLE of the second Supplement-F component satisfies the
source order `b > a > c`.
-/
theorem supplementFTheorem6Second_mle_orders_b_a_c
    {numerator denominator : ℕ} (hnumerator : 0 < numerator)
    (hnumerator_le : numerator ≤ denominator)
    (link : CDFLikePairwiseLink) (reference : Fin 3) (score : ScoreVector (Fin 3))
    (hmle : isPairwiseMLE (supplementFTheorem6SecondDataset numerator denominator)
      link reference score)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ)) :
    score 2 < score 0 ∧ score 0 < score 1 := by
  have hdenominator : 0 < denominator := lt_of_lt_of_le hnumerator hnumerator_le
  constructor
  · apply isPairwiseMLE_score_lt_of_hasOnlyNeighbor_reverse_count_majority
      (supplementFTheorem6SecondDataset numerator denominator) link reference score hmle
      (supplementFTheorem6Second_c_hasOnlyNeighbor_a numerator denominator hdenominator)
      (first := 2) (second := 0)
    all_goals norm_num [supplementFTheorem6SecondDataset]
    all_goals omega
  · apply isPairwiseMLE_score_lt_of_hasOnlyNeighbor_count_majority
      (supplementFTheorem6SecondDataset numerator denominator) link reference score hmle
      (supplementFTheorem6Second_b_hasOnlyNeighbor_a numerator denominator hdenominator)
      (first := 1) (second := 0)
    all_goals norm_num [supplementFTheorem6SecondDataset]
    all_goals omega

/-- The first Supplement-F component graph is strongly connected for every unit fraction. -/
private theorem supplementFTheorem6FirstDataset_stronglyConnected
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    (supplementFTheorem6FirstDataset 1 denominator).isStronglyConnected := by
  have h02 : (supplementFTheorem6FirstDataset 1 denominator).edge 0 2 := by
    change 0 < 5 * denominator + 1
    omega
  have h20 : (supplementFTheorem6FirstDataset 1 denominator).edge 2 0 := by
    change 0 < 5 * denominator - 1
    omega
  have h21 : (supplementFTheorem6FirstDataset 1 denominator).edge 2 1 := by
    change 0 < 100 * denominator
    omega
  have h12 : (supplementFTheorem6FirstDataset 1 denominator).edge 1 2 := by
    change 0 < denominator
    exact hdenominator
  intro first second
  unfold PairwiseCountDataset.reaches
  fin_cases first <;> fin_cases second
  · rfl
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h02) h21
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h02
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h12) h20
  · rfl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h12
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h20
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h21
  · rfl

/-- The second Supplement-F component graph is strongly connected for every unit fraction. -/
private theorem supplementFTheorem6SecondDataset_stronglyConnected
    {denominator : ℕ} (hdenominator : 0 < denominator) :
    (supplementFTheorem6SecondDataset 1 denominator).isStronglyConnected := by
  have h02 : (supplementFTheorem6SecondDataset 1 denominator).edge 0 2 := by
    change 0 < 5 * denominator + 1
    omega
  have h20 : (supplementFTheorem6SecondDataset 1 denominator).edge 2 0 := by
    change 0 < 5 * denominator - 1
    omega
  have h10 : (supplementFTheorem6SecondDataset 1 denominator).edge 1 0 := by
    change 0 < 100 * denominator
    omega
  have h01 : (supplementFTheorem6SecondDataset 1 denominator).edge 0 1 := by
    change 0 < denominator
    exact hdenominator
  intro first second
  unfold PairwiseCountDataset.reaches
  fin_cases first <;> fin_cases second
  · rfl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h01
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h02
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h10
  · rfl
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h10) h02
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h20
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h20) h01
  · rfl

/--
An exact finite Supplement-F witness with the two source component orders and
the reversed pooled `c,a` order refutes Definition 6.1 separability.
-/
theorem supplementFTheorem6_not_separable_of_witness
    {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hnumerator_le : numerator ≤ denominator)
    (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ))
    (firstReference : Fin 3) (firstScore : ScoreVector (Fin 3))
    (hfirstMLE : isPairwiseMLE (supplementFTheorem6FirstDataset numerator denominator)
      link firstReference firstScore)
    (secondReference : Fin 3) (secondScore : ScoreVector (Fin 3))
    (hsecondMLE : isPairwiseMLE (supplementFTheorem6SecondDataset numerator denominator)
      link secondReference secondScore)
    (pooledReference : Fin 3) (pooledScore : ScoreVector (Fin 3))
    (hpooledMLE : isPairwiseMLE (supplementFTheorem6PooledDataset numerator denominator)
      link pooledReference pooledScore)
    (hpooledOrder : pooledScore 0 < pooledScore 2) :
    ¬ pairwiseMLESeparable.{0} link := by
  intro hseparable
  have hfirstOrder := supplementFTheorem6First_mle_orders_a_c_b hnumerator hnumerator_le
    link firstReference firstScore hfirstMLE hcontinuous hstrict
  have hsecondOrder := supplementFTheorem6Second_mle_orders_b_a_c hnumerator hnumerator_le
    link secondReference secondScore hsecondMLE hcontinuous hstrict
  have hpooledMLEAdd :
      isPairwiseMLE
        ((supplementFTheorem6FirstDataset numerator denominator).add
          (supplementFTheorem6SecondDataset numerator denominator))
        link pooledReference pooledScore := by
    rw [supplementFTheorem6_first_add_second hnumerator_le]
    exact hpooledMLE
  have hcontrary : pooledScore 2 < pooledScore 0 := hseparable
    (supplementFTheorem6FirstDataset numerator denominator)
    (supplementFTheorem6SecondDataset numerator denominator)
    firstReference firstScore secondReference secondScore 0 2 hfirstMLE hsecondMLE
    hfirstOrder.2 hsecondOrder.1 pooledReference pooledScore hpooledMLEAdd
  linarith

/--
Source Theorem 6.3. Under the source's strict monotonicity, strict
log-concavity, and differentiability hypotheses, finite MLE violates
separability. The two component MLEs keep `a > c`, while the exact positive
rational pooled witness has `c > a`.
-/
theorem theorem6_3_mle_violates_separability_core
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ)) :
    ¬ pairwiseMLESeparable.{0} link := by
  have hcontinuous : Continuous (link : ℝ → ℝ) := hdifferentiable.continuous
  have hbaseStrong :
      (supplementFTheorem6PooledDataset 0 1).everyComponentStronglyConnected :=
    everyComponentStronglyConnected_of_complete (supplementFTheorem6PooledDataset 0 1)
      supplementFTheorem6PooledBaseDataset_complete
  obtain ⟨baseScore, hbase⟩ := exists_pairwiseMLE_of_everyComponentStronglyConnected
    (supplementFTheorem6PooledDataset 0 1) link 0 hcontinuous hstrict hbaseStrong
  have hbaseConnected : (supplementFTheorem6PooledDataset 0 1).isConnected :=
    isConnected_of_complete (supplementFTheorem6PooledDataset 0 1)
      supplementFTheorem6PooledBaseDataset_complete
  have hbaseUnique : ∀ other,
      isPairwiseMLE (supplementFTheorem6PooledDataset 0 1) link 0 other → other = baseScore := by
    intro other hother
    exact isPairwiseMLE_unique_of_isConnected (supplementFTheorem6PooledDataset 0 1) link
      hlogStrict 0 hbaseConnected baseScore hbase other hother
  have hbaseOrder := supplementFTheorem6PooledBase_mle_orders_c_b_a
    (denominator := 1) (by omega) link hstrict hlogStrict hdifferentiable
    baseScore hbase hbaseUnique
  obtain ⟨uniformBound, huniformBoundPos, huniformBoundLink, huniformScoreBound⟩ :=
    exists_supplementFTheorem6Pooled_uniform_score_bound link hcontinuous hstrict
  let cubeBound : ℝ := max (3 * uniformBound) (scoreSupNorm 0 baseScore)
  have hcubeBoundNonneg : 0 ≤ cubeBound := by
    dsimp [cubeBound]
    exact le_max_of_le_left (by positivity)
  have hbaseCube : ∀ alternative, |baseScore alternative| ≤ cubeBound := by
    intro alternative
    exact (abs_score_le_scoreSupNorm 0 alternative baseScore).trans
      (le_max_of_le_right le_rfl)
  have hpooledMLEExists : ∀ denominator : ℕ, 0 < denominator →
      ∃ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0 score := by
    intro denominator hdenominator
    apply exists_pairwiseMLE_of_everyComponentStronglyConnected
      (supplementFTheorem6PooledDataset 1 denominator) link 0 hcontinuous hstrict
    exact everyComponentStronglyConnected_of_complete
      (supplementFTheorem6PooledDataset 1 denominator)
      (supplementFTheorem6PooledDataset_complete hdenominator)
  have hpooledMLECube : ∀ {denominator : ℕ}, 0 < denominator →
      ∀ score : ScoreVector (Fin 3),
        isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0 score →
          ∀ alternative, |score alternative| ≤ cubeBound := by
    intro denominator hdenominator score hscore alternative
    exact (huniformScoreBound hdenominator score hscore alternative).trans
      (le_max_of_le_left le_rfl)
  obtain ⟨denominator, hdenominator, pooledScore, hpooledMLE, hpooledOrder⟩ :=
    supplementFTheorem6_exists_unitFraction_pooled_mle_order_of_compact
      link hcontinuous hstrict baseScore hbase hbaseUnique (lt_trans hbaseOrder.1 hbaseOrder.2)
      cubeBound hcubeBoundNonneg hbaseCube hpooledMLEExists hpooledMLECube
  have hfirstStrong := supplementFTheorem6FirstDataset_stronglyConnected hdenominator
  obtain ⟨firstScore, hfirstMLE⟩ := exists_pairwiseMLE_of_everyComponentStronglyConnected
    (supplementFTheorem6FirstDataset 1 denominator) link 0 hcontinuous hstrict
    (fun first second _ => hfirstStrong first second)
  have hsecondStrong := supplementFTheorem6SecondDataset_stronglyConnected hdenominator
  obtain ⟨secondScore, hsecondMLE⟩ := exists_pairwiseMLE_of_everyComponentStronglyConnected
    (supplementFTheorem6SecondDataset 1 denominator) link 0 hcontinuous hstrict
    (fun first second _ => hsecondStrong first second)
  exact supplementFTheorem6_not_separable_of_witness (by omega) (by omega) link
    hcontinuous hstrict 0 firstScore hfirstMLE 0 secondScore hsecondMLE
    0 pooledScore hpooledMLE hpooledOrder

/--
Conditional finite closeout of Supplement F. A continuous pooled MLE path
whose base point has `c > a`, together with component MLE existence at the
same exact unit-fraction counts, produces the source's finite separability
counterexample.
-/
theorem supplementFTheorem6_not_separable_of_continuous_pooledMLE_path
    (link : CDFLikePairwiseLink)
    (hcontinuous : Continuous (link : ℝ → ℝ)) (hstrict : StrictMono (link : ℝ → ℝ))
    (pooledScorePath : ℝ → ScoreVector (Fin 3))
    (hpathContinuous : ContinuousAt
      (fun parameter => pooledScorePath parameter 2 - pooledScorePath parameter 0) 0)
    (hbaseOrder : pooledScorePath 0 0 < pooledScorePath 0 2)
    (hfirstMLE : ∀ denominator : ℕ, 0 < denominator →
      ∃ reference score,
        isPairwiseMLE (supplementFTheorem6FirstDataset 1 denominator) link reference score)
    (hsecondMLE : ∀ denominator : ℕ, 0 < denominator →
      ∃ reference score,
        isPairwiseMLE (supplementFTheorem6SecondDataset 1 denominator) link reference score)
    (hpooledMLE : ∀ denominator : ℕ, 0 < denominator →
      isPairwiseMLE (supplementFTheorem6PooledDataset 1 denominator) link 0
        (pooledScorePath ((1 : ℝ) / denominator))) :
    ¬ pairwiseMLESeparable.{0} link := by
  obtain ⟨denominator, hdenominator, hdenominator_one, hpooledOrder⟩ :=
    exists_pos_unitFraction_score_order_of_continuousAt pooledScorePath 0 2
      hpathContinuous hbaseOrder
  obtain ⟨firstReference, firstScore, hfirstScoreMLE⟩ := hfirstMLE denominator hdenominator
  obtain ⟨secondReference, secondScore, hsecondScoreMLE⟩ := hsecondMLE denominator hdenominator
  exact supplementFTheorem6_not_separable_of_witness (by omega) hdenominator_one link
    hcontinuous hstrict firstReference firstScore hfirstScoreMLE secondReference secondScore
    hsecondScoreMLE 0 (pooledScorePath ((1 : ℝ) / denominator))
    (hpooledMLE denominator hdenominator) hpooledOrder

end NoothigattuEtAl2020PairwiseComparisons

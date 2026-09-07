import KR21Monoculture.Mallows
import KR21Monoculture.FirstChoiceDecomposition

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/-- Mallows weights are strictly positive when `q > 0`. -/
theorem mallowsWeight_pos {n : ℕ} {q : ℝ} (hq : 0 < q)
    (ρ π : Ranking n) :
    0 < mallowsWeight q ρ π := by
  unfold mallowsWeight
  exact pow_pos hq _

/-- Mallows weights are nonnegative when `q > 0`. -/
theorem mallowsWeight_nonneg {n : ℕ} {q : ℝ} (hq : 0 < q)
    (ρ π : Ranking n) :
    0 ≤ mallowsWeight q ρ π :=  le_of_lt (mallowsWeight_pos (hq := hq) ρ π)

/-- The finite Mallows partition function is strictly positive when `q > 0`. -/
theorem mallowsPartition_pos {n : ℕ} {q : ℝ} (hq : 0 < q)
    (ρ : Ranking n) :
    0 < mallowsPartition q ρ := by
  classical
  unfold mallowsPartition
  apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg (a₀ := ρ)
  · simpa using mallowsWeight_pos (hq := hq) ρ ρ
  · intro π
    exact mallowsWeight_nonneg (hq := hq) ρ π

/-- The actual finite Mallows PMF obtained by normalizing the real weights. -/
noncomputable def mallowsPMF {n : ℕ} (q : ℝ) (ρ : Ranking n)
    (hq : 0 < q) : PMF (Ranking n) :=
  PMF.ofFintype
    (fun π : Ranking n =>
      ENNReal.ofReal (mallowsWeight q ρ π / mallowsPartition q ρ))
    (by
      classical
      have hpartition_pos : 0 < mallowsPartition q ρ :=
        mallowsPartition_pos (hq := hq) ρ
      have hnonneg :
          ∀ π ∈ (Finset.univ : Finset (Ranking n)),
            0 ≤ mallowsWeight q ρ π / mallowsPartition q ρ := by
        intro π _
        exact div_nonneg (mallowsWeight_nonneg (hq := hq) ρ π)
          (le_of_lt hpartition_pos)
      have hsum :
          (∑ π : Ranking n, mallowsWeight q ρ π / mallowsPartition q ρ) =
            1 := by
        rw [(Finset.sum_div
          (s := (Finset.univ : Finset (Ranking n)))
          (f := fun π : Ranking n => mallowsWeight q ρ π)
          (a := mallowsPartition q ρ)).symm]
        have hsum_pos : 0 < ∑ π : Ranking n, mallowsWeight q ρ π := by
          simpa [mallowsPartition] using hpartition_pos
        unfold mallowsPartition
        field_simp [ne_of_gt hsum_pos]
      calc
        (∑ π : Ranking n,
            ENNReal.ofReal (mallowsWeight q ρ π / mallowsPartition q ρ))
            =
            ENNReal.ofReal
              (∑ π : Ranking n, mallowsWeight q ρ π / mallowsPartition q ρ) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by
              rw [hsum]
              simp)

@[simp] theorem mallowsPMF_apply_toReal {n : ℕ} {q : ℝ}
    (hq : 0 < q) (ρ π : Ranking n) :
    ((mallowsPMF q ρ hq) π).toReal =
      mallowsWeight q ρ π / mallowsPartition q ρ := by
  unfold mallowsPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg (mallowsWeight_nonneg (hq := hq) ρ π)
      (le_of_lt (mallowsPartition_pos (hq := hq) ρ)))

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/-- Concrete finite Mallows specification at center `ρ` and inverse parameter `q`. -/
noncomputable def ofQ (ρ : Ranking n) (q : ℝ) (hq : 0 < q) :
    MallowsSpec n where
  center := ρ
  q := q
  law := mallowsPMF q ρ hq
  partition := mallowsPartition q ρ
  q_pos := hq
  partition_pos := mallowsPartition_pos (hq := hq) ρ
  partition_eq_sum := rfl
  law_apply_toReal := by
    intro π
    exact mallowsPMF_apply_toReal hq ρ π

/-- The center ranking has normalized mass `1 / partition`. -/
@[simp] theorem center_mass_toReal_eq_inv_partition :
    (M.law M.center).toReal = 1 / M.partition := by
  rw [M.law_apply_toReal]
  simp [mallowsWeight_center, one_div]

/-- The center ranking has strictly positive probability under a Mallows law. -/
theorem center_mass_toReal_pos :
    0 < (M.law M.center).toReal := by
  rw [M.center_mass_toReal_eq_inv_partition]
  exact one_div_pos.mpr M.partition_pos

theorem law_apply_toReal_pos (π : Ranking n) :
    0 < (M.law π).toReal := by
  rw [M.law_apply_toReal]
  exact div_pos (mallowsWeight_pos (hq := M.q_pos) M.center π) M.partition_pos

/-- Every first-choice weight is nonnegative. -/
theorem firstWeight_nonneg (c : Candidate n) :
    0 ≤ M.firstWeight c := by
  classical
  unfold firstWeight
  refine Finset.sum_nonneg ?_
  intro π _
  by_cases h : c = firstChoice π
  · have h' : c = π 0 := by simpa [firstChoice] using h
    simpa [h'] using mallowsWeight_nonneg (hq := M.q_pos) M.center π
  · have h' : c ≠ π 0 := by simpa [firstChoice] using h
    simp [h']

/-- Every first/second-choice weight is nonnegative. -/
theorem firstSecondWeight_nonneg (c d : Candidate n) :
    0 ≤ M.firstSecondWeight c d := by
  classical
  unfold firstSecondWeight
  refine Finset.sum_nonneg ?_
  intro π _
  by_cases h : c = firstChoice π ∧ d = secondChoice π
  · have hc : c = π 0 := by simpa [firstChoice] using h.1
    have hd : d = π 1 := by simpa [secondChoice] using h.2
    simpa [hc, hd] using mallowsWeight_nonneg (hq := M.q_pos) M.center π
  · have h' : ¬(c = π 0 ∧ d = π 1) := by
      intro hraw
      apply h
      exact ⟨by simpa [firstChoice] using hraw.1,
        by simpa [secondChoice] using hraw.2⟩
    simp [h']

/-- The center's first-choice fiber contains the center ranking itself. -/
theorem one_le_centerFirstWeight :
    1 ≤ M.firstWeight M.centerFirst := by
  classical
  unfold firstWeight
  have hnonneg :
      ∀ π ∈ (Finset.univ : Finset (Ranking n)),
        0 ≤ if M.centerFirst = firstChoice π then mallowsWeight M.q M.center π else 0 := by
    intro π _
    by_cases h : M.centerFirst = firstChoice π
    · have h' : M.centerFirst = π 0 := by simpa [firstChoice] using h
      simpa [h'] using mallowsWeight_nonneg (hq := M.q_pos) M.center π
    · have h' : M.centerFirst ≠ π 0 := by simpa [firstChoice] using h
      simp [h']
  have hle :
      (if M.centerFirst = firstChoice M.center then mallowsWeight M.q M.center M.center else 0)
        ≤ ∑ π : Ranking n,
            if M.centerFirst = firstChoice π then mallowsWeight M.q M.center π else 0 :=
    Finset.single_le_sum hnonneg (by simp)
  simpa [MallowsSpec.centerFirst, mallowsWeight_center] using hle

/-- The center's top candidate has positive first-choice probability. -/
theorem centerFirstProb_pos :
    0 < firstChoiceProb M.law M.centerFirst := by
  rw [M.centerFirstProb_eq]
  have hweight_pos : 0 < M.firstWeight M.centerFirst :=
    lt_of_lt_of_le zero_lt_one (M.one_le_centerFirstWeight)
  exact div_pos hweight_pos M.partition_pos

/--
The center candidate is missed with positive probability: the ranking that swaps
the center's first two positions has positive Mallows mass.
-/
theorem centerFirstMissProb_pos :
    0 < firstChoiceMissProb M.law M.centerFirst := by
  refine firstChoiceMissProb_pos_of_mass_ne_firstChoice
    (μ := M.law) (c := M.centerFirst) (π₀ := swapTopTwo M.center) ?hne ?hmass
  · simpa [MallowsSpec.centerFirst] using (swapTopTwo_firstChoice_ne M.center).symm
  · exact M.law_apply_toReal_pos (swapTopTwo M.center)

theorem centerFirstProb_lt_one :
    firstChoiceProb M.law M.centerFirst < 1 := by
  have hmiss := M.centerFirstMissProb_pos
  unfold firstChoiceMissProb AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb at hmiss
  unfold firstChoiceProb
  linarith

/-- The center's top-two ordered pair has weight at least one. -/
theorem one_le_centerFirstSecondWeight :
    1 ≤ M.firstSecondWeight M.centerFirst M.centerSecond := by
  classical
  unfold firstSecondWeight
  have hnonneg :
      ∀ π ∈ (Finset.univ : Finset (Ranking n)),
        0 ≤ if M.centerFirst = firstChoice π ∧ M.centerSecond = secondChoice π
            then mallowsWeight M.q M.center π
            else 0 := by
    intro π _
    by_cases h : M.centerFirst = firstChoice π ∧ M.centerSecond = secondChoice π
    · have hf : M.centerFirst = π 0 := by simpa [firstChoice] using h.1
      have hs : M.centerSecond = π 1 := by simpa [secondChoice] using h.2
      simpa [hf, hs] using mallowsWeight_nonneg (hq := M.q_pos) M.center π
    · have h' : ¬(M.centerFirst = π 0 ∧ M.centerSecond = π 1) := by
        intro hraw
        apply h
        exact ⟨by simpa [firstChoice] using hraw.1,
          by simpa [secondChoice] using hraw.2⟩
      simp [h']
  have hle :
      (if M.centerFirst = firstChoice M.center ∧ M.centerSecond = secondChoice M.center
        then mallowsWeight M.q M.center M.center
        else 0)
        ≤ ∑ π : Ranking n,
            if M.centerFirst = firstChoice π ∧ M.centerSecond = secondChoice π
            then mallowsWeight M.q M.center π
            else 0 :=
    Finset.single_le_sum hnonneg (by simp)
  simpa [MallowsSpec.centerFirst, MallowsSpec.centerSecond, mallowsWeight_center] using hle

/-- The center's ordered top-two pair has positive probability. -/
theorem centerFirstSecondProb_pos :
    0 < M.firstSecondChoiceProb M.centerFirst M.centerSecond := by
  rw [M.centerFirstSecondProb_eq]
  have hweight_pos : 0 < M.firstSecondWeight M.centerFirst M.centerSecond :=
    lt_of_lt_of_le zero_lt_one (M.one_le_centerFirstSecondWeight)
  exact div_pos hweight_pos M.partition_pos

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

@[simp] theorem algorithm_centerFirst_eq_human_centerFirst :
    C.algorithm.centerFirst = C.human.centerFirst := by
  simp [MallowsSpec.centerFirst, C.same_center]

@[simp] theorem algorithm_centerSecond_eq_human_centerSecond :
    C.algorithm.centerSecond = C.human.centerSecond := by
  simp [MallowsSpec.centerSecond, C.same_center]

/-- Candidate-sum proof obligations for the Mallows Theorem-3 branch. -/
structure CandidateSumCertificate (value : Candidate n → ℝ) : Prop where
  algorithm_firstChoiceSum_pos :
    0 < ∑ c : Candidate n,
      firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_firstChoiceSum_pos :
    0 < ∑ c : Candidate n,
      firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_competition_firstChoiceSum_pos :
    0 < ∑ c : Candidate n,
      firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c

/-- Candidate-sum positivity is equivalent to Definition 2 for the algorithm law. -/
theorem algorithm_prefersIndependentReranking_iff_candidateSum_pos
    {value : Candidate n → ℝ} :
    Model.PrefersIndependentReranking C.algorithm.law value ↔
      0 < ∑ c : Candidate n,
        firstChoiceMissProb C.algorithm.law c *
          firstChoiceGapMass C.algorithm.law value c := by
  rw [prefersIndependentReranking_iff_firstChoiceGapMassSum_pos]

/-- Candidate-sum positivity is equivalent to Definition 2 for the human law. -/
theorem human_prefersIndependentReranking_iff_candidateSum_pos
    {value : Candidate n → ℝ} :
    Model.PrefersIndependentReranking C.human.law value ↔
      0 < ∑ c : Candidate n,
        firstChoiceMissProb C.human.law c *
          firstChoiceGapMass C.human.law value c := by
  rw [prefersIndependentReranking_iff_firstChoiceGapMassSum_pos]

/-- Candidate-sum positivity is equivalent to Definition 3 for the pair of laws. -/
theorem prefersWeakerCompetition_iff_candidateSum_pos
    {value : Candidate n → ℝ} :
    Model.PrefersWeakerCompetition C.algorithm.law C.human.law value ↔
      0 < ∑ c : Candidate n,
        firstChoiceCollisionDiff C.algorithm.law C.human.law c *
          firstChoiceGapMass C.human.law value c := by
  rw [prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos]

/-- The candidate-sum certificate is a more concrete form of the earlier certificate. -/
theorem finiteLemmaCertificate_of_candidateSumCertificate
    {value : Candidate n → ℝ} (cert : C.CandidateSumCertificate value) :
    C.FiniteLemmaCertificate value := by
  constructor
  · rw [expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass]
    exact cert.algorithm_firstChoiceSum_pos
  · rw [expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass]
    exact cert.human_firstChoiceSum_pos
  · rw [expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass]
    exact cert.weaker_competition_firstChoiceSum_pos

/--
The new first-choice certificate closes the same fixed-parameter target as the
older expectation-level certificate, but is closer to the finite lemmas proved in
Appendix E/F of the paper.
-/
theorem paperHypotheses_of_candidateSumCertificate
    {value : Candidate n → ℝ} (cert : C.CandidateSumCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_certificate
    (C.finiteLemmaCertificate_of_candidateSumCertificate cert)

/-- A convenient name for value vectors that decrease down the common center ranking. -/
def StrictlyCenterOrdered (value : Candidate n → ℝ) : Prop := StrictlyOrderedBy C.algorithm.center value

/-- Under a strictly center-ordered value vector, the center top-two gap is positive. -/
theorem center_valueGap_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ} (hvalue : C.StrictlyCenterOrdered value) :
    0 < valueGap value C.algorithm.center :=  center_valueGap_pos_of_strictlyOrderedBy hvalue

/-- The algorithm law puts positive probability on the common center's top candidate. -/
theorem algorithm_centerFirstProb_pos :
    0 < firstChoiceProb C.algorithm.law C.algorithm.centerFirst :=  C.algorithm.centerFirstProb_pos

/-- The human law also puts positive probability on the common center's top candidate. -/
theorem human_centerFirstProb_pos :
    0 < firstChoiceProb C.human.law C.algorithm.centerFirst := by
  simpa [C.algorithm_centerFirst_eq_human_centerFirst] using C.human.centerFirstProb_pos

/-- The common center's top-two ordered pair has positive probability under the algorithm law. -/
theorem algorithm_centerTopTwoProb_pos :
    0 < C.algorithm.firstSecondChoiceProb C.algorithm.centerFirst C.algorithm.centerSecond :=  C.algorithm.centerFirstSecondProb_pos

/-- The common center's top-two ordered pair has positive probability under the human law. -/
theorem human_centerTopTwoProb_pos :
    0 < C.human.firstSecondChoiceProb C.algorithm.centerFirst C.algorithm.centerSecond := by
  simpa [C.algorithm_centerFirst_eq_human_centerFirst,
    C.algorithm_centerSecond_eq_human_centerSecond] using C.human.centerFirstSecondProb_pos

end MallowsComparison

end KR21Monoculture

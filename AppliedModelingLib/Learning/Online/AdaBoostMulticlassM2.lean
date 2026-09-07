import AppliedModelingLib.Learning.Online.AdaBoost

/-!
# Finite AdaBoost.M2 reduction

This module contains the finite product-space reduction in Freund--Schapire
(1997), Theorem 11.  Each pair of a training example and an incorrect label is
one binary AdaBoost instance.
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

open scoped BigOperators

/-- The incorrect-label binary instances used by AdaBoost.M2. -/
abbrev AdaBoostM2Instance (Training Label : Type*) (label : Training → Label) :=
  { pair : Training × Label // pair.2 ≠ label pair.1 }

/-- At least two labels make the Figure-4 incorrect-label product space nonempty. -/
theorem adaBoostM2Instance_nonempty
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [Fintype Label]
    (label : Training → Label) (hlabels : 1 < Fintype.card Label) :
    Nonempty (AdaBoostM2Instance Training Label label) := by
  classical
  let sample : Training := Classical.choice (inferInstance : Nonempty Training)
  obtain ⟨candidate, hcandidate⟩ := Fintype.exists_ne_of_one_lt_card hlabels (label sample)
  exact ⟨⟨(sample, candidate), hcandidate⟩⟩

/-- The binary weak hypothesis in the AdaBoost.M2 reduction. -/
noncomputable def adaBoostM2BinaryHypothesis
    {Training Label : Type*} [DecidableEq Label]
    (label : Training → Label) (hypothesis : Training → Label → ℝ) :
    AdaBoostM2Instance Training Label label → ℝ :=
  fun pair => (1 / 2 : ℝ) *
    (1 - hypothesis pair.1.1 (label pair.1.1) + hypothesis pair.1.1 pair.1.2)

/-- The finite binary weak-hypothesis list induced by an M2 sequence. -/
noncomputable def adaBoostM2BinaryHypotheses
    {Training Label : Type*} [DecidableEq Label]
    (label : Training → Label) (hypotheses : List (Training → Label → ℝ)) :
    List (AdaBoostM2Instance Training Label label → ℝ) :=
  hypotheses.map (adaBoostM2BinaryHypothesis label)

/-- A unit-valued M2 weak hypothesis induces a unit-valued binary reduction. -/
theorem adaBoostM2BinaryHypothesis_mem_Icc
    {Training Label : Type*} [DecidableEq Label]
    (label : Training → Label) (hypothesis : Training → Label → ℝ)
    (hhypothesis : ∀ sample candidate,
      0 ≤ hypothesis sample candidate ∧ hypothesis sample candidate ≤ 1)
    (pair : AdaBoostM2Instance Training Label label) :
    0 ≤ adaBoostM2BinaryHypothesis label hypothesis pair ∧
      adaBoostM2BinaryHypothesis label hypothesis pair ≤ 1 := by
  unfold adaBoostM2BinaryHypothesis
  rcases hhypothesis pair.1.1 (label pair.1.1) with ⟨htrue_nonneg, htrue_le⟩
  rcases hhypothesis pair.1.1 pair.1.2 with ⟨hcandidate_nonneg, hcandidate_le⟩
  constructor <;> nlinarith

/-- The literal interior-update condition for an AdaBoost.M2 binary reduction. -/
abbrev AdaBoostM2Admissible
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ)) : Prop :=
  AdaBoostAdmissible state (fun _ => 0) (adaBoostM2BinaryHypotheses label hypotheses)

/-- The Figure-4 score of a candidate label at an original training example. -/
noncomputable def adaBoostM2LabelScore
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label)) :
    (hypotheses : List (Training → Label → ℝ)) →
      AdaBoostM2Admissible label state hypotheses → Training → Label → ℝ
  | [], _, _, _ => 0
  | hypothesis :: remaining, hvalid, sample, candidate =>
      adaBoostVoteWeight
          (adaBoostError state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis)) *
        hypothesis sample candidate +
      adaBoostM2LabelScore label
        (adaBoostStep state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis)
          (Classical.choose hvalid)) remaining (Classical.choose_spec hvalid) sample candidate

/-- The Figure-4 final label, realized as a finite maximizer of candidate scores. -/
noncomputable def adaBoostM2FinalHypothesis
    {Training Label : Type*} [Fintype Training] [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) : Training → Label :=
  fun sample =>
    Classical.choose
      (Finset.exists_max_image Finset.univ
        (adaBoostM2LabelScore label state hypotheses hvalid sample) Finset.univ_nonempty)

/-- The binary final hypothesis from the M2 product-space reduction. -/
noncomputable def adaBoostM2BinaryFinalHypothesis
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) :
    AdaBoostM2Instance Training Label label → ℝ :=
  adaBoostFinalHypothesis state (fun _ => 0)
    (adaBoostM2BinaryHypotheses label hypotheses) hvalid

/-- The error list called pseudo-losses in Figure 4. -/
noncomputable def adaBoostM2Errors
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) : List ℝ :=
  adaBoostErrors state (fun _ => 0) (adaBoostM2BinaryHypotheses label hypotheses) hvalid

/-- The Figure-4 product before multiplying by the `k-1` reduction factor. -/
noncomputable def adaBoostM2BinaryTheorem6Factor
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) : ℝ :=
  adaBoostTheorem6Factor state (fun _ => 0)
    (adaBoostM2BinaryHypotheses label hypotheses) hvalid

/-- The binary training error of the Figure-4 product-space reduction. -/
noncomputable def adaBoostM2BinaryTrainingError
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) : ℝ :=
  adaBoostTrainingError state (fun _ => 0)
    (adaBoostM2BinaryHypotheses label hypotheses) hvalid

/-- The product printed in Freund--Schapire Theorem 11. -/
noncomputable def adaBoostM2Theorem11Factor
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) : ℝ :=
  ((Fintype.card Label - 1 : ℕ) : ℝ) *
    adaBoostM2BinaryTheorem6Factor label state hypotheses hvalid

/-- Figure 4's weighted multiclass error under the original example weights. -/
noncomputable def adaBoostM2TrainingError
    {Training Label : Type*} [Fintype Training] [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (exampleWeight : Training → ℝ)
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) : ℝ :=
  ∑ sample, exampleWeight sample *
    (if adaBoostM2FinalHypothesis label state hypotheses hvalid sample = label sample then 0 else 1)

/-- The Figure-4 argmax has score at least that of every candidate label. -/
theorem adaBoostM2FinalHypothesis_score_le
    {Training Label : Type*} [Fintype Training] [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses)
    (sample : Training) (candidate : Label) :
    adaBoostM2LabelScore label state hypotheses hvalid sample candidate ≤
      adaBoostM2LabelScore label state hypotheses hvalid sample
        (adaBoostM2FinalHypothesis label state hypotheses hvalid sample) := by
  classical
  unfold adaBoostM2FinalHypothesis
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ
      (adaBoostM2LabelScore label state hypotheses hvalid sample) Finset.univ_nonempty)).2
    candidate (Finset.mem_univ _)

/-- Twice a reduced binary vote is total vote weight minus true-label score plus candidate score. -/
theorem two_mul_adaBoostM2BinaryVote_eq_weightSum_sub_trueScore_add_candidateScore
    {Training Label : Type*} [Fintype Training] [Fintype Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses)
    (pair : AdaBoostM2Instance Training Label label) :
    2 * adaBoostVote state (fun _ => 0) (adaBoostM2BinaryHypotheses label hypotheses) hvalid pair =
      adaBoostVoteWeightSum state (fun _ => 0) (adaBoostM2BinaryHypotheses label hypotheses) hvalid -
        adaBoostM2LabelScore label state hypotheses hvalid pair.1.1 (label pair.1.1) +
        adaBoostM2LabelScore label state hypotheses hvalid pair.1.1 pair.1.2 := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostVote, adaBoostVoteWeightSum, adaBoostM2LabelScore,
      adaBoostM2BinaryHypotheses]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostM2Admissible label
          (adaBoostStep state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis) herror)
          remaining :=
        Classical.choose_spec hvalid
      have htail := ih
        (state := adaBoostStep state (fun _ => 0)
          (adaBoostM2BinaryHypothesis label hypothesis) herror)
        hrest
      change
        2 *
            (adaBoostVoteWeight
                (adaBoostError state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis)) *
                adaBoostM2BinaryHypothesis label hypothesis pair +
              adaBoostVote
                (adaBoostStep state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis) herror)
                (fun _ => 0) (adaBoostM2BinaryHypotheses label remaining) hrest pair) =
          (adaBoostVoteWeight
              (adaBoostError state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis)) +
            adaBoostVoteWeightSum
              (adaBoostStep state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis) herror)
              (fun _ => 0) (adaBoostM2BinaryHypotheses label remaining) hrest) -
            (adaBoostVoteWeight
                (adaBoostError state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis)) *
                hypothesis pair.1.1 (label pair.1.1) +
              adaBoostM2LabelScore label
                (adaBoostStep state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis) herror)
                remaining hrest pair.1.1 (label pair.1.1)) +
            (adaBoostVoteWeight
                (adaBoostError state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis)) *
                hypothesis pair.1.1 pair.1.2 +
              adaBoostM2LabelScore label
                (adaBoostStep state (fun _ => 0) (adaBoostM2BinaryHypothesis label hypothesis) herror)
                remaining hrest pair.1.1 pair.1.2)
      rw [mul_add, htail]
      unfold adaBoostM2BinaryHypothesis
      ring

/-- A mistaken Figure-4 score argmax yields a binary final-hypothesis mistake at that incorrect label. -/
theorem adaBoostM2FinalHypothesis_mistake_implies_binaryMistake
    {Training Label : Type*} [Fintype Training] [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses)
    (sample : Training)
    (hmistake : adaBoostM2FinalHypothesis label state hypotheses hvalid sample ≠ label sample) :
    adaBoostM2BinaryFinalHypothesis label state hypotheses hvalid
      ⟨(sample, adaBoostM2FinalHypothesis label state hypotheses hvalid sample), hmistake⟩ ≠ 0 := by
  let reduced : AdaBoostM2Instance Training Label label :=
    ⟨(sample, adaBoostM2FinalHypothesis label state hypotheses hvalid sample), hmistake⟩
  have hmax := adaBoostM2FinalHypothesis_score_le label state hypotheses hvalid sample (label sample)
  have hformula := two_mul_adaBoostM2BinaryVote_eq_weightSum_sub_trueScore_add_candidateScore
    label state hypotheses hvalid reduced
  dsimp [reduced] at hformula
  have hthreshold :
      adaBoostVoteWeightSum state (fun _ => 0) (adaBoostM2BinaryHypotheses label hypotheses) hvalid / 2 ≤
        adaBoostVote state (fun _ => 0) (adaBoostM2BinaryHypotheses label hypotheses) hvalid reduced := by
    dsimp [reduced]
    linarith
  change adaBoostM2BinaryFinalHypothesis label state hypotheses hvalid reduced ≠ 0
  simp [adaBoostM2BinaryFinalHypothesis, adaBoostFinalHypothesis, hthreshold]

/-- The Figure-4 initial product weights transfer multiclass error to binary-reduction error. -/
theorem adaBoostM2TrainingError_le_card_sub_one_mul_binaryTrainingError
    {Training Label : Type*} [Fintype Training] [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (exampleWeight : Training → ℝ)
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hlabels : 1 < Fintype.card Label)
    (hinitial : ∀ pair : AdaBoostM2Instance Training Label label,
      state.weight pair = exampleWeight pair.1.1 / ((Fintype.card Label - 1 : ℕ) : ℝ))
    (hypotheses : List (Training → Label → ℝ))
    (hvalid : AdaBoostM2Admissible label state hypotheses) :
    adaBoostM2TrainingError label exampleWeight state hypotheses hvalid ≤
      ((Fintype.card Label - 1 : ℕ) : ℝ) *
        adaBoostM2BinaryTrainingError label state hypotheses hvalid := by
  classical
  let kminus : ℝ := ((Fintype.card Label - 1 : ℕ) : ℝ)
  have hkminus_pos : 0 < kminus := by
    dsimp [kminus]
    exact_mod_cast Nat.sub_pos_of_lt hlabels
  let binaryTerm : AdaBoostM2Instance Training Label label → ℝ := fun pair =>
    state.weight pair *
      (if adaBoostM2BinaryFinalHypothesis label state hypotheses hvalid pair = 0 then 0 else 1)
  have hbinaryTerm_nonneg : ∀ pair, 0 ≤ binaryTerm pair := by
    intro pair
    unfold binaryTerm
    apply mul_nonneg (state.nonneg pair)
    split_ifs <;> norm_num
  have hpointwise : ∀ sample,
      exampleWeight sample *
        (if adaBoostM2FinalHypothesis label state hypotheses hvalid sample = label sample then 0 else 1) ≤
        ∑ pair, if pair.1.1 = sample then kminus * binaryTerm pair else 0 := by
    intro sample
    by_cases hcorrect : adaBoostM2FinalHypothesis label state hypotheses hvalid sample = label sample
    · rw [if_pos hcorrect]
      simp only [mul_zero]
      apply Finset.sum_nonneg
      intro pair _
      split_ifs
      · exact mul_nonneg hkminus_pos.le (hbinaryTerm_nonneg pair)
      · norm_num
    · let pair : AdaBoostM2Instance Training Label label :=
        ⟨(sample, adaBoostM2FinalHypothesis label state hypotheses hvalid sample), hcorrect⟩
      have hbinary := adaBoostM2FinalHypothesis_mistake_implies_binaryMistake
        label state hypotheses hvalid sample hcorrect
      have hpair_first : pair.1.1 = sample := rfl
      have hscale : exampleWeight sample = kminus * binaryTerm pair := by
        unfold binaryTerm
        rw [if_neg hbinary, hinitial pair]
        dsimp [pair, kminus]
        have hk_ne : ((Fintype.card Label - 1 : ℕ) : ℝ) ≠ 0 := by
          exact (by
            exact_mod_cast Nat.sub_pos_of_lt hlabels :
              0 < ((Fintype.card Label - 1 : ℕ) : ℝ)).ne'
        symm
        calc
          ((Fintype.card Label - 1 : ℕ) : ℝ) *
              (exampleWeight sample / ((Fintype.card Label - 1 : ℕ) : ℝ) * 1) =
              exampleWeight sample *
                (((Fintype.card Label - 1 : ℕ) : ℝ) /
                  ((Fintype.card Label - 1 : ℕ) : ℝ)) := by ring
          _ = exampleWeight sample := by rw [div_self hk_ne, mul_one]
      have hsingle : kminus * binaryTerm pair ≤
          ∑ other, if other.1.1 = sample then kminus * binaryTerm other else 0 := by
        have hsubset : ({pair} : Finset (AdaBoostM2Instance Training Label label)) ⊆ Finset.univ := by
          simp
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun other _ _ => by
            split_ifs
            · exact mul_nonneg hkminus_pos.le (hbinaryTerm_nonneg other)
            · norm_num : ∀ other ∈ Finset.univ,
              other ∉ ({pair} : Finset (AdaBoostM2Instance Training Label label)) →
                0 ≤ if other.1.1 = sample then kminus * binaryTerm other else 0)
        simpa [hpair_first] using hsum
      rw [if_neg hcorrect]
      simpa using hscale.trans_le hsingle
  unfold adaBoostM2TrainingError
  calc
    (∑ sample, exampleWeight sample *
      (if adaBoostM2FinalHypothesis label state hypotheses hvalid sample = label sample then 0 else 1)) ≤
        ∑ sample, ∑ pair, if pair.1.1 = sample then kminus * binaryTerm pair else 0 := by
      apply Finset.sum_le_sum
      intro sample _
      exact hpointwise sample
    _ = ∑ pair, kminus * binaryTerm pair := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pair _
      simp
    _ = kminus * ∑ pair, binaryTerm pair := by
      rw [Finset.mul_sum]
    _ = ((Fintype.card Label - 1 : ℕ) : ℝ) *
        adaBoostM2BinaryTrainingError label state hypotheses hvalid := by
      unfold kminus binaryTerm adaBoostM2BinaryTrainingError adaBoostTrainingError
      rfl

/--
Freund--Schapire (1997), Theorem 11, in the finite Figure-4 source model.
The checked product-space reduction gives the source factor `k-1` times the
binary AdaBoost product.
-/
theorem adaBoostM2_training_error_le_theorem11Factor
    {Training Label : Type*} [Fintype Training] [DecidableEq Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (label : Training → Label)
    [Nonempty (AdaBoostM2Instance Training Label label)]
    (exampleWeight : Training → ℝ)
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hstate_total : ∑ pair, state.weight pair = 1)
    (hlabels : 1 < Fintype.card Label)
    (hinitial : ∀ pair : AdaBoostM2Instance Training Label label,
      state.weight pair = exampleWeight pair.1.1 / ((Fintype.card Label - 1 : ℕ) : ℝ))
    (hypotheses : List (Training → Label → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample candidate,
      0 ≤ hypothesis sample candidate ∧ hypothesis sample candidate ≤ 1)
    (hvalid : AdaBoostM2Admissible label state hypotheses) :
    adaBoostM2TrainingError label exampleWeight state hypotheses hvalid ≤
      adaBoostM2Theorem11Factor label state hypotheses hvalid := by
  have hbinary_hypothesis : ∀ hypothesis ∈ adaBoostM2BinaryHypotheses label hypotheses,
      ∀ pair, 0 ≤ hypothesis pair ∧ hypothesis pair ≤ 1 := by
    intro binary hmem pair
    rcases List.mem_map.mp hmem with ⟨hypothesis, hhypothesis_mem, rfl⟩
    exact adaBoostM2BinaryHypothesis_mem_Icc label hypothesis
      (fun sample candidate => hhypothesis hypothesis (by simpa using hhypothesis_mem) sample candidate) pair
  have htransfer := adaBoostM2TrainingError_le_card_sub_one_mul_binaryTrainingError
    label exampleWeight state hlabels hinitial hypotheses hvalid
  have hbinary := adaBoost_training_error_le_theorem6Factor state (fun _ => 0) hstate_total
    (fun _ => ⟨by norm_num, by norm_num⟩) (fun _ => Or.inl rfl)
    (adaBoostM2BinaryHypotheses label hypotheses) hbinary_hypothesis hvalid
  unfold adaBoostM2Theorem11Factor
  exact htransfer.trans
    (mul_le_mul_of_nonneg_left hbinary (by
      exact_mod_cast Nat.zero_le (Fintype.card Label - 1)))

end Online
end Learning
end AppliedModelingLib

import AppliedModelingLib.Learning.Online.AdaBoost

/-!
# Finite multiclass AdaBoost reductions

This module formalizes the finite reduction used by Freund--Schapire (1997),
Theorem 10.  AdaBoost.M1 maps each multiclass weak hypothesis to the binary
indicator of an incorrect prediction, and chooses the final label with maximum
weighted vote.
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

open scoped BigOperators

/-- The binary weak hypothesis in the AdaBoost.M1 reduction: one exactly on mistakes. -/
noncomputable def adaBoostM1BinaryHypothesis
    {Training Label : Type*} [DecidableEq Label]
    (label : Training → Label) (hypothesis : Training → Label) : Training → ℝ :=
  fun sample => if hypothesis sample = label sample then 0 else 1

/-- The binary reduction of a finite AdaBoost.M1 weak-hypothesis sequence. -/
noncomputable def adaBoostM1BinaryHypotheses
    {Training Label : Type*} [DecidableEq Label]
    (label : Training → Label) (hypotheses : List (Training → Label)) : List (Training → ℝ) :=
  hypotheses.map (adaBoostM1BinaryHypothesis label)

/-- The literal interior-update condition for the AdaBoost.M1 binary reduction. -/
def AdaBoostM1Admissible
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label)) : Prop :=
  AdaBoostAdmissible state (fun _ => 0) (adaBoostM1BinaryHypotheses label hypotheses)

/-- The per-label final score in Figure 3 of Freund--Schapire (1997). -/
noncomputable def adaBoostM1LabelScore
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label) :
    (hypotheses : List (Training → Label)) →
      AdaBoostM1Admissible state label hypotheses → Training → Label → ℝ
  | [], _, _, _ => 0
  | hypothesis :: remaining, hvalid, sample, candidate =>
      adaBoostVoteWeight
          (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
        (if hypothesis sample = candidate then 1 else 0) +
      adaBoostM1LabelScore
        (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)
          (Classical.choose hvalid)) label remaining (Classical.choose_spec hvalid) sample candidate

/-- The Figure-3 final label: a finite maximizer of the weighted class votes. -/
noncomputable def adaBoostM1FinalHypothesis
    {Training Label : Type*} [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses) : Training → Label :=
  fun sample =>
    Classical.choose
      (Finset.exists_max_image Finset.univ
        (adaBoostM1LabelScore state label hypotheses hvalid sample) Finset.univ_nonempty)

/-- The binary final hypothesis obtained from the exact M1 reduction. -/
noncomputable def adaBoostM1BinaryFinalHypothesis
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses) : Training → ℝ :=
  adaBoostFinalHypothesis state (fun _ => 0)
    (adaBoostM1BinaryHypotheses label hypotheses) hvalid

/-- The finite weighted multiclass prediction error of the Figure-3 final label. -/
noncomputable def adaBoostM1TrainingError
    {Training Label : Type*} [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses) : ℝ :=
  ∑ sample, state.weight sample *
    (if adaBoostM1FinalHypothesis state label hypotheses hvalid sample = label sample then 0 else 1)

/-- The actual M1 error list, identified with the binary-reduction error list. -/
noncomputable def adaBoostM1Errors
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses) : List ℝ :=
  adaBoostErrors state (fun _ => 0) (adaBoostM1BinaryHypotheses label hypotheses) hvalid

/-- The product printed in Freund--Schapire Theorem 10. -/
noncomputable def adaBoostM1Theorem10Factor
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses) : ℝ :=
  adaBoostTheorem6Factor state (fun _ => 0)
    (adaBoostM1BinaryHypotheses label hypotheses) hvalid

/-- The Figure-3 output is a maximum-score label at every training instance. -/
theorem adaBoostM1FinalHypothesis_score_le
    {Training Label : Type*} [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (sample : Training) (candidate : Label) :
    adaBoostM1LabelScore state label hypotheses hvalid sample candidate ≤
      adaBoostM1LabelScore state label hypotheses hvalid sample
        (adaBoostM1FinalHypothesis state label hypotheses hvalid sample) := by
  classical
  unfold adaBoostM1FinalHypothesis
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ
      (adaBoostM1LabelScore state label hypotheses hvalid sample) Finset.univ_nonempty)).2
    candidate (Finset.mem_univ _)

/-- Each binary M1 hypothesis has values in the source interval `[0,1]`. -/
theorem adaBoostM1BinaryHypothesis_mem_Icc
    {Training Label : Type*} [DecidableEq Label]
    (label : Training → Label) (hypothesis : Training → Label) (sample : Training) :
    0 ≤ adaBoostM1BinaryHypothesis label hypothesis sample ∧
      adaBoostM1BinaryHypothesis label hypothesis sample ≤ 1 := by
  unfold adaBoostM1BinaryHypothesis
  split_ifs <;> norm_num

/-- At the true label, the M1 score plus the binary mistake vote is total vote weight. -/
theorem adaBoostM1LabelScore_trueLabel_add_binaryVote_eq_voteWeightSum
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (sample : Training) :
    adaBoostM1LabelScore state label hypotheses hvalid sample (label sample) +
      adaBoostVote state (fun _ => 0) (adaBoostM1BinaryHypotheses label hypotheses) hvalid sample =
        adaBoostVoteWeightSum state (fun _ => 0)
          (adaBoostM1BinaryHypotheses label hypotheses) hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostM1LabelScore, adaBoostM1BinaryHypotheses,
      adaBoostVote, adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostM1Admissible
          (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
          label remaining :=
        Classical.choose_spec hvalid
      have htail := ih
        (state := adaBoostStep state (fun _ => 0)
          (adaBoostM1BinaryHypothesis label hypothesis) herror)
        hrest
      change
        (adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
            (if hypothesis sample = label sample then 1 else 0) +
          adaBoostM1LabelScore
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            label remaining hrest sample (label sample)) +
          (adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
            adaBoostM1BinaryHypothesis label hypothesis sample +
          adaBoostVote
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            (fun _ => 0) (adaBoostM1BinaryHypotheses label remaining) hrest sample) =
          adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) +
          adaBoostVoteWeightSum
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            (fun _ => 0) (adaBoostM1BinaryHypotheses label remaining) hrest
      rw [← htail]
      unfold adaBoostM1BinaryHypothesis
      split_ifs <;> ring

/-- Two distinct class scores use disjoint vote mass and are bounded by total vote weight. -/
theorem adaBoostM1LabelScore_add_le_voteWeightSum_of_ne
    {Training Label : Type*} [Fintype Training] [Nonempty Training] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostM1Errors state label hypotheses hvalid, error ≤ 1 / 2)
    (sample : Training) (first second : Label) (hdistinct : first ≠ second) :
    adaBoostM1LabelScore state label hypotheses hvalid sample first +
      adaBoostM1LabelScore state label hypotheses hvalid sample second ≤
        adaBoostVoteWeightSum state (fun _ => 0)
          (adaBoostM1BinaryHypotheses label hypotheses) hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostM1LabelScore, adaBoostM1BinaryHypotheses, adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostM1Admissible
          (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
          label remaining :=
        Classical.choose_spec hvalid
      have hhead : adaBoostError state (fun _ => 0)
          (adaBoostM1BinaryHypothesis label hypothesis) ≤ 1 / 2 := by
        apply hweak
        simp [adaBoostM1Errors, adaBoostM1BinaryHypotheses, adaBoostErrors]
      have hweak_rest : ∀ error ∈
          adaBoostM1Errors
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            label remaining hrest,
          error ≤ 1 / 2 := by
        intro error hmem
        change error ∈ adaBoostErrors
          (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
          (fun _ => 0) (adaBoostM1BinaryHypotheses label remaining) hrest at hmem
        apply hweak error
        change error ∈ adaBoostError state (fun _ => 0)
          (adaBoostM1BinaryHypothesis label hypothesis) ::
            adaBoostErrors
              (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
              (fun _ => 0) (adaBoostM1BinaryHypotheses label remaining) hrest
        simp [hmem]
      have hcoefficient_nonneg :
          0 ≤ adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) :=
        adaBoostVoteWeight_nonneg_of_error_le_half ⟨herror.1, hhead⟩
      have hindicator :
          (if hypothesis sample = first then (1 : ℝ) else 0) +
            (if hypothesis sample = second then (1 : ℝ) else 0) ≤ 1 := by
        by_cases hfirst : hypothesis sample = first
        · have hsecond : hypothesis sample ≠ second := by
            intro hsecond
            apply hdistinct
            calc
              first = hypothesis sample := hfirst.symm
              _ = second := hsecond
          simp [hfirst, hdistinct]
        · by_cases hsecond : hypothesis sample = second
          · have hsecond_first : second ≠ first := Ne.symm hdistinct
            simp [hsecond, hsecond_first]
          · simp [hfirst, hsecond]
      have hhead_le :
          adaBoostVoteWeight
              (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
              (if hypothesis sample = first then (1 : ℝ) else 0) +
            adaBoostVoteWeight
              (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
              (if hypothesis sample = second then (1 : ℝ) else 0) ≤
            adaBoostVoteWeight
              (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) := by
        nlinarith
      have htail := ih
        (state := adaBoostStep state (fun _ => 0)
          (adaBoostM1BinaryHypothesis label hypothesis) herror)
        hrest hweak_rest
      change
        (adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
            (if hypothesis sample = first then 1 else 0) +
          adaBoostM1LabelScore
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            label remaining hrest sample first) +
          (adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) *
            (if hypothesis sample = second then 1 else 0) +
          adaBoostM1LabelScore
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            label remaining hrest sample second) ≤
          adaBoostVoteWeight
            (adaBoostError state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis)) +
          adaBoostVoteWeightSum
            (adaBoostStep state (fun _ => 0) (adaBoostM1BinaryHypothesis label hypothesis) herror)
            (fun _ => 0) (adaBoostM1BinaryHypotheses label remaining) hrest
      linarith

/-- A mistaken Figure-3 argmax is a mistake of the binary AdaBoost reduction. -/
theorem adaBoostM1FinalHypothesis_mistake_implies_binaryMistake
    {Training Label : Type*} [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostM1Errors state label hypotheses hvalid, error ≤ 1 / 2)
    (sample : Training)
    (hmistake : adaBoostM1FinalHypothesis state label hypotheses hvalid sample ≠ label sample) :
    adaBoostM1BinaryFinalHypothesis state label hypotheses hvalid sample ≠ 0 := by
  have hmax := adaBoostM1FinalHypothesis_score_le state label hypotheses hvalid sample
    (label sample)
  have hpair := adaBoostM1LabelScore_add_le_voteWeightSum_of_ne
    state label hypotheses hvalid hweak sample (label sample)
    (adaBoostM1FinalHypothesis state label hypotheses hvalid sample) hmistake.symm
  have hcorrect_le_half :
      adaBoostM1LabelScore state label hypotheses hvalid sample (label sample) ≤
        adaBoostVoteWeightSum state (fun _ => 0)
          (adaBoostM1BinaryHypotheses label hypotheses) hvalid / 2 := by
    linarith
  have hscore_identity := adaBoostM1LabelScore_trueLabel_add_binaryVote_eq_voteWeightSum
    state label hypotheses hvalid sample
  have hthreshold :
      adaBoostVoteWeightSum state (fun _ => 0)
          (adaBoostM1BinaryHypotheses label hypotheses) hvalid / 2 ≤
        adaBoostVote state (fun _ => 0)
          (adaBoostM1BinaryHypotheses label hypotheses) hvalid sample := by
    linarith
  simp [adaBoostM1BinaryFinalHypothesis, adaBoostFinalHypothesis, hthreshold]

/-- The finite Figure-3 multiclass error is bounded by the error of its binary AdaBoost reduction. -/
theorem adaBoostM1TrainingError_le_binaryTrainingError
    {Training Label : Type*} [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostM1Errors state label hypotheses hvalid, error ≤ 1 / 2) :
    adaBoostM1TrainingError state label hypotheses hvalid ≤
      adaBoostTrainingError state (fun _ => 0)
        (adaBoostM1BinaryHypotheses label hypotheses) hvalid := by
  unfold adaBoostM1TrainingError adaBoostTrainingError
  apply Finset.sum_le_sum
  intro sample _
  change state.weight sample *
      (if adaBoostM1FinalHypothesis state label hypotheses hvalid sample = label sample then 0 else 1) ≤
    state.weight sample *
      (if adaBoostM1BinaryFinalHypothesis state label hypotheses hvalid sample = 0 then 0 else 1)
  by_cases hcorrect : adaBoostM1FinalHypothesis state label hypotheses hvalid sample = label sample
  · rw [if_pos hcorrect]
    have hindicator : 0 ≤
        (if adaBoostM1BinaryFinalHypothesis state label hypotheses hvalid sample = 0 then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    simpa using mul_nonneg (state.nonneg sample) hindicator
  · have hbinary := adaBoostM1FinalHypothesis_mistake_implies_binaryMistake
      state label hypotheses hvalid hweak sample hcorrect
    rw [if_neg hcorrect, if_neg hbinary]

/--
Freund--Schapire (1997), Theorem 10, in its finite source model.  The concrete
AdaBoost.M1 score argmax reduces to the binary mistake-indicator run and hence
inherits the printed Theorem-6 product.
-/
theorem adaBoostM1_training_error_le_theorem10Factor
    {Training Label : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostM1Errors state label hypotheses hvalid, error ≤ 1 / 2) :
    adaBoostM1TrainingError state label hypotheses hvalid ≤
      adaBoostM1Theorem10Factor state label hypotheses hvalid := by
  have hbinary_hypothesis : ∀ hypothesis ∈ adaBoostM1BinaryHypotheses label hypotheses,
      ∀ sample, 0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1 := by
    intro binary hmem sample
    rcases List.mem_map.mp hmem with ⟨hypothesis, hhypothesis, rfl⟩
    exact adaBoostM1BinaryHypothesis_mem_Icc label hypothesis sample
  calc
    adaBoostM1TrainingError state label hypotheses hvalid ≤
        adaBoostTrainingError state (fun _ => 0)
          (adaBoostM1BinaryHypotheses label hypotheses) hvalid :=
      adaBoostM1TrainingError_le_binaryTrainingError state label hypotheses hvalid hweak
    _ ≤ adaBoostTheorem6Factor state (fun _ => 0)
        (adaBoostM1BinaryHypotheses label hypotheses) hvalid :=
      adaBoost_training_error_le_theorem6Factor state (fun _ => 0) hstate_total
        (fun _ => ⟨by norm_num, by norm_num⟩) (fun _ => Or.inl rfl)
        (adaBoostM1BinaryHypotheses label hypotheses) hbinary_hypothesis hvalid
    _ = adaBoostM1Theorem10Factor state label hypotheses hvalid := rfl

end Online
end Learning
end AppliedModelingLib

import GHKR22BiasBounties.Core
import AppliedModelingLib.Foundations.Probability.FiniteIidUniformLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Adaptive certificate checking

This file gives executable semantics for Algorithm 2 and proves the deterministic
soundness/completeness implication used by Theorem 11.  It then discharges the
needed uniform deviation event with the library's finite-family Hoeffding
theorem.  Sparse transcripts are encoded by their accepted positions, so the
candidate family grows polynomially in the submission horizon for a fixed
acceptance budget and the confidence bound depends only logarithmically on the
horizon.
-/

namespace GHKR22BiasBounties

noncomputable section

open scoped BigOperators
open AppliedModelingLib Probability

/-- One proposed `(current model, group, replacement model)` triple. -/
structure Submission (X Y : Type*) where
  current : Model X Y
  group : Group X
  replacement : Model X Y

/-- The signed, mass-weighted improvement on one labelled example. -/
def submissionScore {X Y : Type*} (loss : BoundedLoss Y)
    (submission : Submission X Y) (datum : X × Y) : ℝ :=
  groupIndicator submission.group datum.1 *
    (datumLoss loss submission.current datum -
      datumLoss loss submission.replacement datum)

/-- Affine normalization of the signed score from `[-1,1]` to `[0,1]`. -/
def normalizedSubmissionScore {X Y : Type*} (loss : BoundedLoss Y)
    (submission : Submission X Y) (datum : X × Y) : ℝ :=
  (submissionScore loss submission datum + 1) / 2

/-- The signed submission score is always in `[-1,1]`. -/
theorem submissionScore_mem_Icc {X Y : Type*} (loss : BoundedLoss Y)
    (submission : Submission X Y) (datum : X × Y) :
    submissionScore loss submission datum ∈ Set.Icc (-1 : ℝ) 1 := by
  have hcurrent_nonneg := loss.nonneg (submission.current datum.1) datum.2
  have hcurrent_one := loss.le_one (submission.current datum.1) datum.2
  have hreplacement_nonneg := loss.nonneg (submission.replacement datum.1) datum.2
  have hreplacement_one := loss.le_one (submission.replacement datum.1) datum.2
  cases hg : submission.group datum.1
  · simp [submissionScore, groupIndicator, datumLoss, hg]
  · simp only [submissionScore, groupIndicator,
      AppliedModelingLib.Learning.Prediction.hardGroupIndicator, hg,
      ↓reduceIte, one_mul]
    unfold datumLoss
    constructor <;> linarith

/-- The normalized score is `[0,1]`-valued, as required by Hoeffding. -/
theorem normalizedSubmissionScore_mem_Icc {X Y : Type*}
    (loss : BoundedLoss Y) (submission : Submission X Y) (datum : X × Y) :
    normalizedSubmissionScore loss submission datum ∈ Set.Icc (0 : ℝ) 1 := by
  rcases submissionScore_mem_Icc loss submission datum with ⟨hlower, hupper⟩
  constructor <;> unfold normalizedSubmissionScore <;> linarith

/-- Population expectation of the pointwise score is the certificate objective. -/
theorem pmfExp_submissionScore_eq_certificateImprovementScore
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (submission : Submission X Y) :
    AppliedModelingLib.pmfExp law (submissionScore loss submission) =
      certificateImprovementScore law loss submission.current
        submission.group submission.replacement := by
  calc
    AppliedModelingLib.pmfExp law (submissionScore loss submission) =
        groupLossNumerator law loss submission.current submission.group -
          groupLossNumerator law loss submission.replacement submission.group := by
      unfold groupLossNumerator
      rw [← AppliedModelingLib.pmfExp_sub]
      apply AppliedModelingLib.pmfExp_congr
      intro datum
      unfold submissionScore datumLoss
      ring
    _ = certificateImprovementScore law loss submission.current
          submission.group submission.replacement :=
      (certificateImprovementScore_eq_numerator_sub_total law loss
        submission.current submission.group submission.replacement).symm

/-- Population expectation of the normalized score. -/
theorem pmfExp_normalizedSubmissionScore
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (submission : Submission X Y) :
    AppliedModelingLib.pmfExp law (normalizedSubmissionScore loss submission) =
      (certificateImprovementScore law loss submission.current
        submission.group submission.replacement + 1) / 2 := by
  unfold normalizedSubmissionScore
  simp_rw [div_eq_mul_inv, add_mul]
  rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_mul_const,
    AppliedModelingLib.pmfExp_mul_const, AppliedModelingLib.pmfExp_const,
    pmfExp_submissionScore_eq_certificateImprovementScore]

/-- Empirical mass-weighted improvement on an `n`-sample holdout. -/
def empiricalSubmissionScore {X Y : Type*} {n : ℕ}
    (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (submission : Submission X Y) : ℝ :=
  finiteIidScoreSum (submissionScore loss submission) sample / (n : ℝ)

/-- Algorithm 2's output alphabet. -/
inductive CertificateDecision where
  | rejected
  | accepted
deriving DecidableEq, Repr

/-- Algorithm 2's exact threshold rule for one proposed submission. -/
def certificateCheckerDecision {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (submission : Submission X Y) : CertificateDecision :=
  if empiricalSubmissionScore loss sample submission < 3 * epsilon / 4 then
    .rejected
  else
    .accepted

/-- Accepted exactly when the empirical score reaches `3 epsilon / 4`. -/
theorem certificateCheckerDecision_eq_accepted_iff {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (submission : Submission X Y) :
    certificateCheckerDecision epsilon loss sample submission = .accepted ↔
      3 * epsilon / 4 ≤ empiricalSubmissionScore loss sample submission := by
  unfold certificateCheckerDecision
  by_cases h : empiricalSubmissionScore loss sample submission < 3 * epsilon / 4
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

/-- Rejected exactly when the empirical score is below `3 epsilon / 4`. -/
theorem certificateCheckerDecision_eq_rejected_iff {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (submission : Submission X Y) :
    certificateCheckerDecision epsilon loss sample submission = .rejected ↔
      empiricalSubmissionScore loss sample submission < 3 * epsilon / 4 := by
  unfold certificateCheckerDecision
  by_cases h : empiricalSubmissionScore loss sample submission < 3 * epsilon / 4
  · simp [h]
  · simp [h]

/-- Number of accepts in a finite transcript. -/
def numberAccepted : List CertificateDecision → ℕ :=
  List.count .accepted

/-- Zero-based accepted positions in a public transcript. -/
def acceptedPositions : List CertificateDecision → List ℕ
  | [] => []
  | .rejected :: rest => (acceptedPositions rest).map Nat.succ
  | .accepted :: rest => 0 :: (acceptedPositions rest).map Nat.succ

/-- The operational counter equals the length of the literal sparse position
list. -/
theorem acceptedPositions_length (transcript : List CertificateDecision) :
    (acceptedPositions transcript).length = numberAccepted transcript := by
  induction transcript with
  | nil => simp [acceptedPositions, numberAccepted]
  | cons decision rest ih =>
      cases decision <;> simp [acceptedPositions, numberAccepted, ih]

/-- Position `i` appears in the sparse list exactly when transcript entry `i`
is accepted. -/
theorem nat_mem_acceptedPositions_iff (transcript : List CertificateDecision)
    (i : ℕ) (hi : i < transcript.length) :
    i ∈ acceptedPositions transcript ↔ transcript[i] = .accepted := by
  induction transcript generalizing i with
  | nil => simp at hi
  | cons decision rest ih =>
      cases i with
      | zero =>
          cases decision <;> simp [acceptedPositions]
      | succ i =>
          have hiRest : i < rest.length := by simpa using hi
          cases decision <;> simp [acceptedPositions, ih i hiRest]

/-- Specialized membership characterization for zero-based accepted
positions. -/
theorem mem_acceptedPositions_iff (transcript : List CertificateDecision)
    (i : Fin transcript.length) :
    i.1 ∈ acceptedPositions transcript ↔ transcript.get i = .accepted := by
  simpa [List.get_eq_getElem] using
    nat_mem_acceptedPositions_iff transcript i.1 i.2

/-- Every recorded accepted position lies inside the transcript. -/
theorem acceptedPosition_lt_length (transcript : List CertificateDecision)
    {position : ℕ} (hposition : position ∈ acceptedPositions transcript) :
    position < transcript.length := by
  induction transcript generalizing position with
  | nil => simp [acceptedPositions] at hposition
  | cons decision rest ih =>
      cases decision
      · simp only [acceptedPositions] at hposition
        rcases List.mem_map.mp hposition with ⟨tailPosition, htail, rfl⟩
        have := ih htail
        simp only [List.length_cons]
        omega
      · simp only [acceptedPositions, List.mem_cons] at hposition
        rcases hposition with rfl | hposition
        · simp
        · rcases List.mem_map.mp hposition with ⟨tailPosition, htail, rfl⟩
          have := ih htail
          simp only [List.length_cons]
          omega

/-- An adaptive submitter may use the entire public transcript. -/
abbrev AdaptiveSubmissionStrategy (X Y : Type*) :=
  List CertificateDecision → Submission X Y

/--
Algorithm 2 as a terminating recursive state machine.  The remaining-round
counter realizes the horizon `U`; the real-valued guard is the one printed in
the paper.
-/
def certificateCheckerRunAux {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (strategy : AdaptiveSubmissionStrategy X Y) :
    ℕ → List CertificateDecision → List CertificateDecision
  | 0, reverseTranscript => reverseTranscript.reverse
  | remaining + 1, reverseTranscript =>
      if (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon then
        let publicTranscript := reverseTranscript.reverse
        let submission := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample submission
        certificateCheckerRunAux epsilon loss sample strategy remaining
          (decision :: reverseTranscript)
      else
        reverseTranscript.reverse

/-- Algorithm 2 run for at most `U` submissions. -/
def certificateCheckerRun {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (U : ℕ) (strategy : AdaptiveSubmissionStrategy X Y) :
    List CertificateDecision :=
  certificateCheckerRunAux epsilon loss sample strategy U []

/-- A length-`K` code of acceptance positions, padded by position `U`. -/
abbrev SparseTranscriptCode (U K : ℕ) := Fin K → Fin (U + 1)

/-- Every possible round and sparse public transcript has one query index. -/
abbrev AdaptiveQueryIndex (U K : ℕ) := Fin U × SparseTranscriptCode U K

/-- Exact size of the sparse transcript coding family. -/
theorem card_sparseTranscriptCode (U K : ℕ) :
    Fintype.card (SparseTranscriptCode U K) = (U + 1) ^ K := by
  simp [SparseTranscriptCode]

/-- Exact number of round/transcript query indices. -/
theorem card_adaptiveQueryIndex (U K : ℕ) :
    Fintype.card (AdaptiveQueryIndex U K) = U * (U + 1) ^ K := by
  simp [AdaptiveQueryIndex, SparseTranscriptCode]

/-- Encode the first `K` accepted positions of a transcript, padding unused
slots by the sentinel `U`.  Under the later premise `numberAccepted ≤ K`, no
accepted position is omitted. -/
noncomputable def encodeSparseTranscript (U K : ℕ)
    (transcript : List CertificateDecision) (hlength : transcript.length < U) :
    SparseTranscriptCode U K := by
  classical
  intro slot
  if hslot : slot.1 < (acceptedPositions transcript).length then
    let position := (acceptedPositions transcript).get ⟨slot.1, hslot⟩
    exact ⟨position, Nat.lt_succ_of_lt
      ((acceptedPosition_lt_length transcript (List.get_mem _ _)).trans hlength)⟩
  else
    exact ⟨U, Nat.lt_succ_self U⟩

/-- Decode a sparse position code into the public transcript preceding a
given query round. -/
noncomputable def decodeSparseTranscript (U K : ℕ)
    (round : Fin U) (code : SparseTranscriptCode U K) :
    List CertificateDecision := by
  classical
  exact List.ofFn fun position : Fin round.1 =>
    if ∃ slot : Fin K, (code slot).1 = position.1 then
      .accepted
    else
      .rejected

/-- A position is named by the sparse encoding exactly when that transcript
entry is accepted, provided the transcript has at most `K` accepts. -/
theorem exists_encodeSparseTranscript_eq_iff (U K : ℕ)
    (transcript : List CertificateDecision) (hlength : transcript.length < U)
    (hcount : numberAccepted transcript ≤ K) (position : Fin transcript.length) :
    (∃ slot : Fin K,
      (encodeSparseTranscript U K transcript hlength slot).1 = position.1) ↔
      transcript.get position = .accepted := by
  classical
  constructor
  · rintro ⟨slot, hslot⟩
    unfold encodeSparseTranscript at hslot
    split at hslot
    · rename_i hwithin
      have hmem :
          (acceptedPositions transcript).get ⟨slot.1, hwithin⟩ ∈
            acceptedPositions transcript := List.get_mem _ _
      have heq :
          (acceptedPositions transcript).get ⟨slot.1, hwithin⟩ = position.1 := by
        simpa using hslot
      exact (mem_acceptedPositions_iff transcript position).mp (heq ▸ hmem)
    · have heq : U = position.1 := by simpa using hslot
      have := position.2
      omega
  · intro haccepted
    have hmem : position.1 ∈ acceptedPositions transcript :=
      (mem_acceptedPositions_iff transcript position).mpr haccepted
    rcases List.mem_iff_get.mp hmem with ⟨positionIndex, hget⟩
    have hindexLt : positionIndex.1 < K := by
      have hlengthAccepted := acceptedPositions_length transcript
      omega
    let slot : Fin K := ⟨positionIndex.1, hindexLt⟩
    refine ⟨slot, ?_⟩
    unfold encodeSparseTranscript
    simp only [slot]
    split
    · rename_i hwithin
      simpa using hget
    · rename_i houtside
      exact False.elim (houtside positionIndex.2)

/-- Encoding then decoding recovers every transcript whose length and number
of accepts fit the declared sparse horizon. -/
theorem decodeSparseTranscript_encode (U K : ℕ)
    (transcript : List CertificateDecision) (hlength : transcript.length < U)
    (hcount : numberAccepted transcript ≤ K) :
    decodeSparseTranscript U K ⟨transcript.length, hlength⟩
        (encodeSparseTranscript U K transcript hlength) = transcript := by
  classical
  apply List.ext_getElem
  · simp [decodeSparseTranscript]
  · intro position hdecoded htranscript
    have hiff := exists_encodeSparseTranscript_eq_iff U K transcript hlength hcount
      ⟨position, htranscript⟩
    simp only [decodeSparseTranscript, List.getElem_ofFn]
    by_cases hexists : ∃ slot : Fin K,
        (encodeSparseTranscript U K transcript hlength slot).1 = position
    · have haccepted : transcript.get ⟨position, htranscript⟩ = .accepted :=
        hiff.mp (by simpa using hexists)
      simp [hexists, List.get_eq_getElem] at haccepted ⊢
      exact haccepted.symm
    · have hnotAccepted : transcript.get ⟨position, htranscript⟩ ≠ .accepted := by
        intro haccepted
        exact hexists (by simpa using hiff.mpr haccepted)
      have hrejected : transcript.get ⟨position, htranscript⟩ = .rejected := by
        cases hdecision : transcript.get ⟨position, htranscript⟩ <;> simp_all
      simp [hexists, List.get_eq_getElem] at hrejected ⊢
      exact hrejected.symm

/-- The finite query family induced by an arbitrary transcript-adaptive
submission strategy. -/
noncomputable def sparseStrategyFamily {X Y : Type*}
    (U K : ℕ) (strategy : AdaptiveSubmissionStrategy X Y) :
    AdaptiveQueryIndex U K → Submission X Y :=
  fun query => strategy (decodeSparseTranscript U K query.1 query.2)

/-- Every query made after a public transcript of length below `U` and with at
most `K` accepts belongs to the finite sparse strategy family. -/
theorem strategy_submission_mem_sparseFamily {X Y : Type*}
    (U K : ℕ) (strategy : AdaptiveSubmissionStrategy X Y)
    (transcript : List CertificateDecision) (hlength : transcript.length < U)
    (hcount : numberAccepted transcript ≤ K) :
    ∃ query : AdaptiveQueryIndex U K,
      sparseStrategyFamily U K strategy query = strategy transcript := by
  let round : Fin U := ⟨transcript.length, hlength⟩
  let code := encodeSparseTranscript U K transcript hlength
  refine ⟨(round, code), ?_⟩
  simp only [sparseStrategyFamily, round, code]
  rw [decodeSparseTranscript_encode U K transcript hlength hcount]

/-- Uniform population/empirical score accuracy for a candidate family. -/
def CheckerUniformlyAccurate {X Y Θ : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (epsilon : ℝ) {n : ℕ}
    (sample : Fin n → X × Y) : Prop :=
  ∀ parameter,
    |empiricalSubmissionScore loss sample (family parameter) -
      certificateImprovementScore law loss (family parameter).current
        (family parameter).group (family parameter).replacement| ≤ epsilon / 4

/-- Uniform accuracy of the sparse family transfers to every query that an
arbitrary transcript-adaptive strategy can make within its acceptance budget. -/
theorem strategy_query_accurate_of_sparseFamily
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (U K : ℕ) (strategy : AdaptiveSubmissionStrategy X Y)
    (epsilon : ℝ) {n : ℕ} (sample : Fin n → X × Y)
    (haccurate : CheckerUniformlyAccurate law loss
      (sparseStrategyFamily U K strategy) epsilon sample)
    (transcript : List CertificateDecision) (hlength : transcript.length < U)
    (hcount : numberAccepted transcript ≤ K) :
    |empiricalSubmissionScore loss sample (strategy transcript) -
      certificateImprovementScore law loss (strategy transcript).current
        (strategy transcript).group (strategy transcript).replacement| ≤ epsilon / 4 := by
  rcases strategy_submission_mem_sparseFamily U K strategy transcript hlength hcount with
    ⟨query, hquery⟩
  simpa [hquery] using haccurate query

/-- Normalized Hoeffding event whose complement yields checker accuracy. -/
def adaptiveCheckerDeviationEvent {X Y Θ : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (epsilon : ℝ) {n : ℕ}
    (sample : Fin n → X × Y) : Prop :=
  finiteIidUniformScoreDeviationEvent law
    (fun parameter => normalizedSubmissionScore loss (family parameter))
    Set.univ (epsilon / 8) sample

/-- The probability of the normalized deviation event. -/
def adaptiveCheckerDeviationFailure {X Y Θ : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (epsilon : ℝ) (n : ℕ) : ℝ :=
  finiteIidUniformScoreDeviationFailure law
    (fun parameter => normalizedSubmissionScore loss (family parameter))
    Set.univ (epsilon / 8) n

/-- Normalized and raw centered sums differ by exactly a factor of two. -/
theorem normalized_centered_sum_eq_half_raw_centered
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (submission : Submission X Y) (n : ℕ) (sample : Fin n → X × Y) :
    finiteIidScoreSum (normalizedSubmissionScore loss submission) sample -
        (n : ℝ) * AppliedModelingLib.pmfExp law
          (normalizedSubmissionScore loss submission) =
      (finiteIidScoreSum (submissionScore loss submission) sample -
        (n : ℝ) * certificateImprovementScore law loss submission.current
          submission.group submission.replacement) / 2 := by
  rw [pmfExp_normalizedSubmissionScore]
  unfold finiteIidScoreSum normalizedSubmissionScore
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Outside the Hoeffding event, every candidate has checker-scale accuracy. -/
theorem checkerUniformlyAccurate_of_not_deviationEvent
    {X Y Θ : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (n : ℕ) (hcount : 0 < n) (sample : Fin n → X × Y)
    (hgood : ¬ adaptiveCheckerDeviationEvent law loss family epsilon sample) :
    CheckerUniformlyAccurate law loss family epsilon sample := by
  intro parameter
  have hnormalized :
      |finiteIidScoreSum
          (normalizedSubmissionScore loss (family parameter)) sample -
        (n : ℝ) * AppliedModelingLib.pmfExp law
          (normalizedSubmissionScore loss (family parameter))| ≤
        (n : ℝ) * (epsilon / 8) := by
    by_contra hnot
    exact hgood ⟨parameter, Set.mem_univ _, lt_of_not_ge hnot⟩
  rw [normalized_centered_sum_eq_half_raw_centered] at hnormalized
  have hraw :
      |finiteIidScoreSum (submissionScore loss (family parameter)) sample -
        (n : ℝ) * certificateImprovementScore law loss
          (family parameter).current (family parameter).group
          (family parameter).replacement| ≤
        (n : ℝ) * (epsilon / 4) := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hnormalized
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  unfold empiricalSubmissionScore
  have hn : (0 : ℝ) < n := by exact_mod_cast hcount
  have hrewrite :
      finiteIidScoreSum
            (submissionScore loss (family parameter)) sample /
          (n : ℝ) -
          certificateImprovementScore law loss
            (family parameter).current (family parameter).group
            (family parameter).replacement =
        (finiteIidScoreSum
            (submissionScore loss (family parameter)) sample -
          (n : ℝ) * certificateImprovementScore law loss
            (family parameter).current (family parameter).group
            (family parameter).replacement) / (n : ℝ) := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hn]
  exact (div_le_iff₀ hn).2 (by
    calc
      |finiteIidScoreSum
          (submissionScore loss (family parameter)) sample -
        (n : ℝ) * certificateImprovementScore law loss
          (family parameter).current (family parameter).group
          (family parameter).replacement| ≤
          (n : ℝ) * (epsilon / 4) := hraw
      _ = epsilon / 4 * (n : ℝ) := by ring)

/-- Hoeffding failure bound for the entire sparse adaptive query family. -/
theorem adaptiveCheckerDeviationFailure_le_hoeffding
    {X Y Θ : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Fintype Θ] [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (epsilon : ℝ) (n : ℕ)
    (hcount : 0 < n) (hepsilon : 0 ≤ epsilon) :
    adaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (Fintype.card Θ : ℝ) * 2 *
        Real.exp (-2 * (n : ℝ) * (epsilon / 8) ^ 2) := by
  exact finiteIidUniformScoreDeviationFailure_le_hoeffding law
    (fun parameter => normalizedSubmissionScore loss (family parameter))
    Set.univ (epsilon / 8) n hcount (div_nonneg hepsilon (by norm_num))
    (fun parameter datum => normalizedSubmissionScore_mem_Icc loss (family parameter) datum)

/-- The same confidence bound with the paper's exponent `-n epsilon² / 32`. -/
theorem adaptiveCheckerDeviationFailure_le_explicit
    {X Y Θ : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Fintype Θ] [TopologicalSpace Θ]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (family : Θ → Submission X Y) (epsilon : ℝ) (n : ℕ)
    (hcount : 0 < n) (hepsilon : 0 ≤ epsilon) :
    adaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (Fintype.card Θ : ℝ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  convert adaptiveCheckerDeviationFailure_le_hoeffding law loss family epsilon n
    hcount hepsilon using 1 <;> ring

/-- Theorem 11(a): rejection rules out every certificate of score at least epsilon. -/
theorem certificateChecker_rejected_sound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y}
    {epsilon : ℝ} {n : ℕ} {sample : Fin n → X × Y}
    {submission : Submission X Y}
    (haccurate :
      |empiricalSubmissionScore loss sample submission -
        certificateImprovementScore law loss submission.current
          submission.group submission.replacement| ≤ epsilon / 4)
    (hdecision :
      certificateCheckerDecision epsilon loss sample submission = .rejected) :
    ∀ mu Delta, epsilon ≤ mu * Delta →
      ¬ CertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta := by
  intro mu Delta hlarge hcert
  have hempirical :=
    (certificateCheckerDecision_eq_rejected_iff epsilon loss sample submission).mp hdecision
  have hpopulation :
      certificateImprovementScore law loss submission.current
        submission.group submission.replacement < epsilon := by
    rcases abs_le.mp haccurate with ⟨hlower, hupper⟩
    linarith
  have hcertScore := certificate_mul_le_improvementScore hcert
  linarith

/-- Theorem 11(b): acceptance certifies population score at least epsilon/2. -/
theorem certificateChecker_accepted_complete
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {n : ℕ} {sample : Fin n → X × Y}
    {submission : Submission X Y}
    (haccurate :
      |empiricalSubmissionScore loss sample submission -
        certificateImprovementScore law loss submission.current
          submission.group submission.replacement| ≤ epsilon / 4)
    (hdecision :
      certificateCheckerDecision epsilon loss sample submission = .accepted) :
    ∃ mu Delta,
      CertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta ∧
      epsilon / 2 ≤ mu * Delta := by
  have hempirical :=
    (certificateCheckerDecision_eq_accepted_iff epsilon loss sample submission).mp hdecision
  have hpopulation : epsilon / 2 ≤
      certificateImprovementScore law loss submission.current
        submission.group submission.replacement := by
    rcases abs_le.mp haccurate with ⟨hlower, hupper⟩
    linarith
  have hpositive : 0 < certificateImprovementScore law loss submission.current
      submission.group submission.replacement := lt_of_lt_of_le (half_pos hepsilon) hpopulation
  refine ⟨groupMass law submission.group,
    groupLoss law loss submission.current submission.group -
      groupLoss law loss submission.replacement submission.group,
    canonical_certificate_of_positive_score hpositive, ?_⟩
  simpa [certificateImprovementScore] using hpopulation

/--
Theorem 11, deterministic high-probability-event content, uniformly over every
round/transcript query in an adaptive candidate family.
-/
theorem theorem11_certificateChecker_guarantees
    {X Y Θ : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y}
    {family : Θ → Submission X Y} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {n : ℕ} {sample : Fin n → X × Y}
    (haccurate : CheckerUniformlyAccurate law loss family epsilon sample) :
    (∀ parameter mu Delta,
        certificateCheckerDecision epsilon loss sample (family parameter) = .rejected →
        epsilon ≤ mu * Delta →
        ¬ CertificateOfSuboptimality law loss (family parameter).current
          (family parameter).group (family parameter).replacement mu Delta) ∧
      (∀ parameter,
        certificateCheckerDecision epsilon loss sample (family parameter) = .accepted →
        ∃ mu Delta,
          CertificateOfSuboptimality law loss (family parameter).current
            (family parameter).group (family parameter).replacement mu Delta ∧
          epsilon / 2 ≤ mu * Delta) := by
  constructor
  · intro parameter mu Delta hdecision hlarge
    exact certificateChecker_rejected_sound (haccurate parameter) hdecision mu Delta hlarge
  · intro parameter hdecision
    exact certificateChecker_accepted_complete hepsilon (haccurate parameter) hdecision

/-! ## Theorem 11 for the actual transcript-adaptive runner -/

/-- Source conclusions for one realized checker decision. -/
def CheckerDecisionGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (submission : Submission X Y) (decision : CertificateDecision) : Prop :=
  (decision = .rejected →
    ∀ mu Delta, epsilon ≤ mu * Delta →
      ¬ CertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta) ∧
  (decision = .accepted →
    ∃ mu Delta,
      CertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta ∧
      epsilon / 2 ≤ mu * Delta)

/-- Every query actually issued by the recursive Algorithm 2 runner has the
source's rejection/acceptance semantics. -/
def CheckerRunAuxGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y)
    (strategy : AdaptiveSubmissionStrategy X Y) :
    ℕ → List CertificateDecision → Prop
  | 0, _ => True
  | remaining + 1, reverseTranscript =>
      if (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon then
        let publicTranscript := reverseTranscript.reverse
        let submission := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample submission
        CheckerDecisionGuaranteed law loss epsilon submission decision ∧
          CheckerRunAuxGuaranteed law loss epsilon sample strategy remaining
            (decision :: reverseTranscript)
      else
        True

/-- Public transcript reversal preserves the number of accepted decisions. -/
@[simp] theorem numberAccepted_reverse (transcript : List CertificateDecision) :
    numberAccepted transcript.reverse = numberAccepted transcript := by
  simp [numberAccepted]

/-- Integer acceptance budget corresponding to the source guard
`NumberAccepted ≤ 2 / epsilon`. -/
noncomputable def checkerAcceptanceBudget (epsilon : ℝ) : ℕ :=
  Nat.floor (2 / epsilon)

/-- Any natural counter passing the real-valued source guard fits the rounded
sparse-transcript budget. -/
theorem numberAccepted_le_checkerAcceptanceBudget
    (epsilon : ℝ) (transcript : List CertificateDecision)
    (hguard : (numberAccepted transcript : ℝ) ≤ 2 / epsilon) :
    numberAccepted transcript ≤ checkerAcceptanceBudget epsilon := by
  unfold checkerAcceptanceBudget
  exact Nat.le_floor hguard

/-- The literal non-strict source guard may record one final acceptance after
the queried prefix has reached the rounded budget.  No later query is issued
from that transcript, so every queried prefix still has at most the budget
used by the sparse-family proof. -/
theorem certificateCheckerRunAux_numberAccepted_le_budget_add_one
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (strategy : AdaptiveSubmissionStrategy X Y) (hepsilon : 0 < epsilon) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      numberAccepted reverseTranscript ≤ checkerAcceptanceBudget epsilon + 1 →
      numberAccepted
          (certificateCheckerRunAux epsilon loss sample strategy remaining
            reverseTranscript) ≤
        checkerAcceptanceBudget epsilon + 1 := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript hcount
      simpa [certificateCheckerRunAux] using hcount
  | succ remaining ih =>
      intro reverseTranscript hcount
      simp only [certificateCheckerRunAux]
      split
      · rename_i hguard
        apply ih
        have hbudget := numberAccepted_le_checkerAcceptanceBudget
          epsilon reverseTranscript hguard
        have hbudget' : List.count CertificateDecision.accepted reverseTranscript ≤
            checkerAcceptanceBudget epsilon := by
          simpa [numberAccepted] using hbudget
        cases hdecision : certificateCheckerDecision epsilon loss sample
            (strategy reverseTranscript.reverse) <;>
          simp [numberAccepted, hdecision] <;> omega
      · simpa using hcount

/-- Algorithm 2's complete public transcript has at most one more acceptance
than the sparse-prefix budget induced by its printed non-strict guard. -/
theorem certificateCheckerRun_numberAccepted_le_budget_add_one
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (U : ℕ) (strategy : AdaptiveSubmissionStrategy X Y)
    (hepsilon : 0 < epsilon) :
    numberAccepted (certificateCheckerRun epsilon loss sample U strategy) ≤
      checkerAcceptanceBudget epsilon + 1 := by
  unfold certificateCheckerRun
  apply certificateCheckerRunAux_numberAccepted_le_budget_add_one
    epsilon loss sample strategy hepsilon U []
  simp [numberAccepted]

/-- Uniform accuracy of the sparse family implies the advertised guarantees
for every query in the literal recursive checker execution. -/
theorem checkerRunAuxGuaranteed_of_sparseFamilyAccuracy
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (U : ℕ) (strategy : AdaptiveSubmissionStrategy X Y)
    (haccurate : CheckerUniformlyAccurate law loss
      (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
      epsilon sample) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      reverseTranscript.length + remaining ≤ U →
      CheckerRunAuxGuaranteed law loss epsilon sample strategy
        remaining reverseTranscript := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _
      trivial
  | succ remaining ih =>
      intro reverseTranscript hlength
      simp only [CheckerRunAuxGuaranteed]
      split
      · rename_i hguard
        let publicTranscript := reverseTranscript.reverse
        let submission := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hpublicLength : publicTranscript.length < U := by
          dsimp [publicTranscript]
          simp only [List.length_reverse]
          omega
        have hpublicCount :
            numberAccepted publicTranscript ≤ checkerAcceptanceBudget epsilon := by
          dsimp [publicTranscript]
          rw [numberAccepted_reverse]
          exact numberAccepted_le_checkerAcceptanceBudget epsilon reverseTranscript hguard
        have hqueryAccurate := strategy_query_accurate_of_sparseFamily
          law loss U (checkerAcceptanceBudget epsilon) strategy epsilon sample
          haccurate publicTranscript hpublicLength hpublicCount
        constructor
        · constructor
          · intro hdecision mu Delta hlarge
            exact certificateChecker_rejected_sound hqueryAccurate hdecision
              mu Delta hlarge
          · intro hdecision
            exact certificateChecker_accepted_complete hepsilon hqueryAccurate hdecision
        · apply ih
          simp only [List.length_cons]
          omega
      · trivial

/-- Actual Algorithm 2 execution guarantee from the empty initial transcript. -/
theorem theorem11_certificateCheckerRun_guaranteed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (U : ℕ) (strategy : AdaptiveSubmissionStrategy X Y)
    (haccurate : CheckerUniformlyAccurate law loss
      (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
      epsilon sample) :
    CheckerRunAuxGuaranteed law loss epsilon sample strategy U [] := by
  exact checkerRunAuxGuaranteed_of_sparseFamilyAccuracy
    law loss epsilon hepsilon sample U strategy haccurate U [] (by simp)

/-- Failure probability for the literal transcript-adaptive Algorithm 2 run. -/
noncomputable def certificateCheckerRunGuaranteeFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n U : ℕ) (strategy : AdaptiveSubmissionStrategy X Y) : ℝ := by
  classical
  exact pmfProb (pmfProduct (Fin n) (X × Y) law) (fun sample =>
    ¬ CheckerRunAuxGuaranteed law loss epsilon sample strategy U [])

/-- Bad actual runs are contained in the finite sparse-family deviation event. -/
theorem certificateCheckerRunGuaranteeFailure_le_deviationFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (hcount : 0 < n) (strategy : AdaptiveSubmissionStrategy X Y) :
    certificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
      letI : TopologicalSpace
          (AdaptiveQueryIndex U (checkerAcceptanceBudget epsilon)) := ⊤
      adaptiveCheckerDeviationFailure law loss
        (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
        epsilon n := by
  classical
  letI : TopologicalSpace
      (AdaptiveQueryIndex U (checkerAcceptanceBudget epsilon)) := ⊤
  unfold certificateCheckerRunGuaranteeFailure adaptiveCheckerDeviationFailure
    finiteIidUniformScoreDeviationFailure
  apply pmfProb_le_of_imp
  intro sample hbad
  by_contra hdeviation
  apply hbad
  apply theorem11_certificateCheckerRun_guaranteed
    law loss epsilon hepsilon sample U strategy
  exact checkerUniformlyAccurate_of_not_deviationEvent law loss
    (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
    epsilon hepsilon.le n hcount sample hdeviation

/-- Theorem 11's complete exact probability bound for an arbitrary
transcript-adaptive strategy and the literal Algorithm 2 runner. -/
theorem theorem11_adaptive_certificateCheckerRun
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (hcount : 0 < n) (strategy : AdaptiveSubmissionStrategy X Y) :
    certificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
      (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  letI : TopologicalSpace
      (AdaptiveQueryIndex U (checkerAcceptanceBudget epsilon)) := ⊤
  calc
    certificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
        adaptiveCheckerDeviationFailure law loss
          (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
          epsilon n :=
      certificateCheckerRunGuaranteeFailure_le_deviationFailure
        law loss epsilon hepsilon n U hcount strategy
    _ ≤ (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
      simpa [card_adaptiveQueryIndex] using
        (adaptiveCheckerDeviationFailure_le_explicit law loss
          (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
          epsilon n hcount hepsilon.le)

/--
Remark 13 in exact form: after sparse-transcript encoding, the visible failure
bound depends on `U` and `K`, but has no term for the syntactic or VC complexity
of submitted groups and models.
-/
theorem remark13_sparse_adaptive_failure_bound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (U K : ℕ) (family : AdaptiveQueryIndex U K → Submission X Y)
    (epsilon : ℝ) (n : ℕ) (hcount : 0 < n) (hepsilon : 0 ≤ epsilon) :
    letI : TopologicalSpace (AdaptiveQueryIndex U K) := ⊤
    adaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (U * (U + 1) ^ K : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  letI : TopologicalSpace (AdaptiveQueryIndex U K) := ⊤
  simpa [card_adaptiveQueryIndex] using
    (adaptiveCheckerDeviationFailure_le_explicit law loss family epsilon n
      hcount hepsilon)

end

end GHKR22BiasBounties

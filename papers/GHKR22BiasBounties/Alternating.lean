import GHKR22BiasBounties.TernaryCSC
import Mathlib.Tactic.Linarith

/-!
# Alternating certificate optimization

This file proves Lemmas 21--22 and a corrected Theorem 23.  Lemma 22 is
formalized through the exact disagreement-sample identity, avoiding the
normalization and set-partition slips in the printed proof.

The printed Algorithm 6 can return immediately after changing `g`, at which
point its `h` need not be a best response to the new group.  The executable
algorithm below is the minimal robust repair: compute both coordinate
best-response gaps at the current pair, update a coordinate whose gain exceeds
`epsilon`, and halt only if neither gap does.  Every update gains more than
`epsilon` in an objective contained in `[-1,1]`, yielding the same
`2 / epsilon` update bound and the advertised two-sided local guarantee.
-/

namespace GHKR22BiasBounties

noncomputable section

/-- The binary certificate objective used by Algorithms 5--6. -/
def binaryCertificateObjective {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (g : Group X) (h : Model X Bool) : ℝ :=
  certificateImprovementScore law binaryZeroOneLoss current g h

/-- Fixed-group ERM over a binary model class. -/
def GroupRestrictedERM {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (g : Group X)
    (H : Set (Model X Bool)) (hStar : Model X Bool) : Prop :=
  hStar ∈ H ∧ ∀ h ∈ H,
    groupLossNumerator law binaryZeroOneLoss hStar g ≤
      groupLossNumerator law binaryZeroOneLoss h g

/-- Lemma 21: group-restricted ERM is the fixed-group objective maximizer. -/
theorem lemma21_groupERM_maximizes_fixed_group
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (g : Group X) (H : Set (Model X Bool)) (hStar : Model X Bool)
    (herm : GroupRestrictedERM law g H hStar) :
    hStar ∈ H ∧ ∀ h ∈ H,
      binaryCertificateObjective law current g h ≤
        binaryCertificateObjective law current g hStar := by
  refine ⟨herm.1, ?_⟩
  intro h hh
  rw [binaryCertificateObjective,
    certificateImprovementScore_eq_numerator_sub_total,
    binaryCertificateObjective,
    certificateImprovementScore_eq_numerator_sub_total]
  linarith [herm.2 h hh]

/-- Pseudo-label on a point where current model and replacement disagree. -/
def disagreementLabel {X : Type*} (replacement : Model X Bool)
    (datum : X × Bool) : Bool :=
  replacement datum.1 = datum.2

/--
Unnormalized empirical-risk objective on the disagreement sample `D_h`.
Points where the two models agree contribute zero and therefore do not affect
the argmin.
-/
def disagreementGroupLoss {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current replacement : Model X Bool)
    (g : Group X) : ℝ :=
  AppliedModelingLib.pmfExp law (fun datum =>
    if current datum.1 = replacement datum.1 then 0
    else binaryZeroOneLoss.value (g datum.1) (disagreementLabel replacement datum))

/-- Population mass on disagreements where the replacement is correct. -/
def replacementAdvantageMass {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current replacement : Model X Bool) : ℝ :=
  AppliedModelingLib.pmfExp law (fun datum =>
    if current datum.1 ≠ replacement datum.1 ∧
        replacement datum.1 = datum.2 then 1 else 0)

/-- Pointwise identity behind the group-ERM reduction. -/
theorem disagreement_pointwise_identity {X : Type*}
    (current replacement : Model X Bool) (g : Group X) (datum : X × Bool) :
    groupIndicator g datum.1 *
        (binaryZeroOneLoss.value (current datum.1) datum.2 -
          binaryZeroOneLoss.value (replacement datum.1) datum.2) =
      (if current datum.1 ≠ replacement datum.1 ∧
          replacement datum.1 = datum.2 then 1 else 0) -
        (if current datum.1 = replacement datum.1 then 0
          else binaryZeroOneLoss.value (g datum.1)
            (disagreementLabel replacement datum)) := by
  cases hcurrent : current datum.1 <;> cases hreplacement : replacement datum.1 <;>
    cases hg : g datum.1 <;> cases htruth : datum.2 <;>
    simp [groupIndicator, binaryZeroOneLoss, disagreementLabel,
      hcurrent, hreplacement, hg, htruth]

/-- Exact objective decomposition used in Lemma 22. -/
theorem binaryCertificateObjective_eq_advantage_sub_disagreementLoss
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current replacement : Model X Bool)
    (g : Group X) :
    binaryCertificateObjective law current g replacement =
      replacementAdvantageMass law current replacement -
        disagreementGroupLoss law current replacement g := by
  rw [binaryCertificateObjective,
    certificateImprovementScore_eq_numerator_sub_total]
  unfold groupLossNumerator replacementAdvantageMass disagreementGroupLoss
  rw [← AppliedModelingLib.pmfExp_sub, ← AppliedModelingLib.pmfExp_sub]
  apply AppliedModelingLib.pmfExp_congr
  intro datum
  calc
    groupIndicator g datum.1 * datumLoss binaryZeroOneLoss current datum -
        groupIndicator g datum.1 * datumLoss binaryZeroOneLoss replacement datum =
      groupIndicator g datum.1 *
        (binaryZeroOneLoss.value (current datum.1) datum.2 -
          binaryZeroOneLoss.value (replacement datum.1) datum.2) := by
            simp only [datumLoss]
            ring
    _ = (if current datum.1 ≠ replacement datum.1 ∧
          replacement datum.1 = datum.2 then 1 else 0) -
        (if current datum.1 = replacement datum.1 then 0
          else binaryZeroOneLoss.value (g datum.1)
            (disagreementLabel replacement datum)) :=
      disagreement_pointwise_identity current replacement g datum

/-- ERM over the corrected disagreement sample. -/
def DisagreementERM {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current replacement : Model X Bool)
    (G : Set (Group X)) (gStar : Group X) : Prop :=
  gStar ∈ G ∧ ∀ g ∈ G,
    disagreementGroupLoss law current replacement gStar ≤
      disagreementGroupLoss law current replacement g

/-- Lemma 22: disagreement-sample ERM maximizes the fixed-model objective. -/
theorem lemma22_disagreementERM_maximizes_fixed_model
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current replacement : Model X Bool)
    (G : Set (Group X)) (gStar : Group X)
    (herm : DisagreementERM law current replacement G gStar) :
    gStar ∈ G ∧ ∀ g ∈ G,
      binaryCertificateObjective law current g replacement ≤
        binaryCertificateObjective law current gStar replacement := by
  refine ⟨herm.1, ?_⟩
  intro g hg
  rw [binaryCertificateObjective_eq_advantage_sub_disagreementLoss,
    binaryCertificateObjective_eq_advantage_sub_disagreementLoss]
  linarith [herm.2 g hg]

/-- A group/model pair considered by the coordinate optimizer. -/
structure CertificatePair (X : Type*) where
  group : Group X
  replacement : Model X Bool

/-- Exact coordinate best-response oracles over classes `G` and `H`. -/
structure CoordinateBestResponses {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool)) where
  bestGroup : Model X Bool → Group X
  bestModel : Group X → Model X Bool
  bestGroup_mem : ∀ h, bestGroup h ∈ G
  bestModel_mem : ∀ g, bestModel g ∈ H
  bestGroup_max : ∀ h g, g ∈ G →
    binaryCertificateObjective law current g h ≤
      binaryCertificateObjective law current (bestGroup h) h
  bestModel_max : ∀ g h, h ∈ H →
    binaryCertificateObjective law current g h ≤
      binaryCertificateObjective law current g (bestModel g)

/-- Membership of a candidate pair in `G × H`. -/
def PairAdmissible {X : Type*} (G : Set (Group X))
    (H : Set (Model X Bool)) (pair : CertificatePair X) : Prop :=
  pair.group ∈ G ∧ pair.replacement ∈ H

/-- The repaired Theorem 23 local-optimality predicate. -/
def EpsilonCoordinatewiseLocal {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (G : Set (Group X)) (H : Set (Model X Bool))
    (epsilon : ℝ) (pair : CertificatePair X) : Prop :=
  PairAdmissible G H pair ∧
    (∀ h ∈ H,
      binaryCertificateObjective law current pair.group h ≤
        binaryCertificateObjective law current pair.group pair.replacement + epsilon) ∧
    (∀ g ∈ G,
      binaryCertificateObjective law current g pair.replacement ≤
        binaryCertificateObjective law current pair.group pair.replacement + epsilon)

/--
One corrected coordinate-ascent step.  Model best response is tested first;
if it has no large gain, the group best response is tested.
-/
def coordinateAscentStep {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (pair : CertificatePair X) : Option (CertificatePair X) :=
  let modelResponse : CertificatePair X :=
    { group := pair.group, replacement := oracle.bestModel pair.group }
  if binaryCertificateObjective law current pair.group pair.replacement + epsilon <
      binaryCertificateObjective law current modelResponse.group
        modelResponse.replacement then
    some modelResponse
  else
    let groupResponse : CertificatePair X :=
      { group := oracle.bestGroup pair.replacement,
        replacement := pair.replacement }
    if binaryCertificateObjective law current pair.group pair.replacement + epsilon <
        binaryCertificateObjective law current groupResponse.group
          groupResponse.replacement then
      some groupResponse
    else
      none

/-- A halted corrected coordinate step is an epsilon local optimum. -/
theorem epsilonCoordinatewiseLocal_of_coordinateAscentStep_eq_none
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (pair : CertificatePair X) (hpair : PairAdmissible G H pair)
    (hhalt : coordinateAscentStep law current epsilon oracle pair = none) :
    EpsilonCoordinatewiseLocal law current G H epsilon pair := by
  unfold coordinateAscentStep at hhalt
  dsimp only at hhalt
  split at hhalt
  · contradiction
  next hmodel =>
    split at hhalt
    · contradiction
    next hgroup =>
      refine ⟨hpair, ?_, ?_⟩
      · intro h hh
        exact le_trans (oracle.bestModel_max pair.group h hh) (by
          exact le_of_not_gt hmodel)
      · intro g hg
        exact le_trans (oracle.bestGroup_max pair.replacement g hg) (by
          exact le_of_not_gt hgroup)

/-- Any successful coordinate step stays admissible. -/
theorem pairAdmissible_of_coordinateAscentStep_eq_some
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (pair next : CertificatePair X) (hpair : PairAdmissible G H pair)
    (hstep : coordinateAscentStep law current epsilon oracle pair = some next) :
    PairAdmissible G H next := by
  unfold coordinateAscentStep at hstep
  dsimp only at hstep
  split at hstep
  · simp only [Option.some.injEq] at hstep
    subst next
    exact ⟨hpair.1, oracle.bestModel_mem pair.group⟩
  next _ =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst next
      exact ⟨oracle.bestGroup_mem pair.replacement, hpair.2⟩
    · contradiction

/-- Every successful coordinate step improves objective by more than epsilon. -/
theorem coordinateAscentStep_improves
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (pair next : CertificatePair X)
    (hstep : coordinateAscentStep law current epsilon oracle pair = some next) :
    binaryCertificateObjective law current pair.group pair.replacement + epsilon <
      binaryCertificateObjective law current next.group next.replacement := by
  unfold coordinateAscentStep at hstep
  dsimp only at hstep
  split at hstep
  next hmodel =>
    simp only [Option.some.injEq] at hstep
    subst next
    exact hmodel
  next _ =>
    split at hstep
    next hgroup =>
      simp only [Option.some.injEq] at hstep
      subst next
      exact hgroup
    next _ => contradiction

/-- Fuelled executable corrected Algorithm 6. -/
def coordinateAscentLoop {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H) :
    ℕ → CertificatePair X → Option (CertificatePair X)
  | 0, pair =>
      match coordinateAscentStep law current epsilon oracle pair with
      | none => some pair
      | some _ => none
  | fuel + 1, pair =>
      match coordinateAscentStep law current epsilon oracle pair with
      | none => some pair
      | some next => coordinateAscentLoop law current epsilon oracle fuel next

/-- Every successful corrected Algorithm 6 result is epsilon-coordinatewise local. -/
theorem theorem23_coordinateAscentLoop_local
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (fuel : ℕ) (initial output : CertificatePair X)
    (hinitial : PairAdmissible G H initial)
    (houtput : coordinateAscentLoop law current epsilon oracle fuel initial = some output) :
    EpsilonCoordinatewiseLocal law current G H epsilon output := by
  induction fuel generalizing initial with
  | zero =>
      unfold coordinateAscentLoop at houtput
      cases hstep : coordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact epsilonCoordinatewiseLocal_of_coordinateAscentStep_eq_none
            law current epsilon oracle initial hinitial hstep
      | some next => simp [hstep] at houtput
  | succ fuel ih =>
      unfold coordinateAscentLoop at houtput
      cases hstep : coordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact epsilonCoordinatewiseLocal_of_coordinateAscentStep_eq_none
            law current epsilon oracle initial hinitial hstep
      | some next =>
          simp only [hstep] at houtput
          exact ih next
            (pairAdmissible_of_coordinateAscentStep_eq_some law current epsilon
              oracle initial next hinitial hstep)
            houtput

/-- A successful corrected Algorithm 6 run never lowers its objective when
`epsilon` is nonnegative.  In particular, a positive initial certificate
remains positive at termination. -/
theorem coordinateAscentLoop_objective_mono
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (fuel : ℕ) (initial output : CertificatePair X)
    (houtput : coordinateAscentLoop law current epsilon oracle fuel initial =
      some output) :
    binaryCertificateObjective law current initial.group initial.replacement ≤
      binaryCertificateObjective law current output.group output.replacement := by
  induction fuel generalizing initial with
  | zero =>
      unfold coordinateAscentLoop at houtput
      cases hstep : coordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact le_rfl
      | some next => simp [hstep] at houtput
  | succ fuel ih =>
      unfold coordinateAscentLoop at houtput
      cases hstep : coordinateAscentStep law current epsilon oracle initial with
      | none =>
          simp [hstep] at houtput
          subst output
          exact le_rfl
      | some next =>
          simp only [hstep] at houtput
          have hfirst := coordinateAscentStep_improves
            law current epsilon oracle initial next hstep
          have htail := ih next houtput
          exact le_trans (by linarith) htail

/-- Fuel exhaustion exposes `fuel + 1` strict coordinate improvements. -/
theorem coordinateAscentLoop_none_objective_budget
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (fuel : ℕ) (initial : CertificatePair X)
    (hexhausted : coordinateAscentLoop law current epsilon oracle fuel initial = none) :
    ∃ final : CertificatePair X,
      binaryCertificateObjective law current initial.group initial.replacement +
          ((fuel : ℝ) + 1) * epsilon <
        binaryCertificateObjective law current final.group final.replacement := by
  induction fuel generalizing initial with
  | zero =>
      unfold coordinateAscentLoop at hexhausted
      cases hstep : coordinateAscentStep law current epsilon oracle initial with
      | none => simp [hstep] at hexhausted
      | some next =>
          refine ⟨next, ?_⟩
          have himproves := coordinateAscentStep_improves
            law current epsilon oracle initial next hstep
          simpa using himproves
  | succ fuel ih =>
      unfold coordinateAscentLoop at hexhausted
      cases hstep : coordinateAscentStep law current epsilon oracle initial with
      | none => simp [hstep] at hexhausted
      | some next =>
          simp only [hstep] at hexhausted
          obtain ⟨final, htail⟩ := ih next hexhausted
          have hfirst := coordinateAscentStep_improves
            law current epsilon oracle initial next hstep
          refine ⟨final, ?_⟩
          push_cast
          nlinarith

/-- The binary certificate objective always lies in `[-1,1]`. -/
theorem binaryCertificateObjective_mem_Icc
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (pair : CertificatePair X) :
    binaryCertificateObjective law current pair.group pair.replacement ∈
      Set.Icc (-1 : ℝ) 1 := by
  rw [binaryCertificateObjective,
    ← pmfExp_submissionScore_eq_certificateImprovementScore law binaryZeroOneLoss
      { current := current, group := pair.group,
        replacement := pair.replacement }]
  constructor
  · have hnonneg := AppliedModelingLib.pmfExp_nonneg_of_forall_nonneg law
        (fun datum => submissionScore binaryZeroOneLoss
          { current := current, group := pair.group,
            replacement := pair.replacement } datum + 1)
        (fun datum => by
          have hbound := (submissionScore_mem_Icc binaryZeroOneLoss
            { current := current, group := pair.group,
              replacement := pair.replacement } datum).1
          linarith)
    rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const] at hnonneg
    linarith
  · exact AppliedModelingLib.pmfExp_le_of_forall_le law _ 1
      (fun datum => (submissionScore_mem_Icc binaryZeroOneLoss
        { current := current, group := pair.group,
          replacement := pair.replacement } datum).2)

/-- The corrected Algorithm 6 terminates once the supplied fuel covers the
objective range `[-1,1]`. -/
theorem coordinateAscentLoop_terminates_of_budget
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) (_hepsilon : 0 < epsilon)
    {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (fuel : ℕ) (hbudget : 2 ≤ ((fuel : ℝ) + 1) * epsilon)
    (initial : CertificatePair X) :
    ∃ output,
      coordinateAscentLoop law current epsilon oracle fuel initial = some output := by
  cases hresult : coordinateAscentLoop law current epsilon oracle fuel initial with
  | some output => exact ⟨output, rfl⟩
  | none =>
      obtain ⟨final, himproves⟩ := coordinateAscentLoop_none_objective_budget
        law current epsilon oracle fuel initial hresult
      have hinitial := binaryCertificateObjective_mem_Icc law current initial
      have hfinal := binaryCertificateObjective_mem_Icc law current final
      rcases hinitial with ⟨hinitialLower, _⟩
      rcases hfinal with ⟨_, hfinalUpper⟩
      exfalso
      nlinarith

/-- Total corrected Theorem 23 local-optimality endpoint. -/
theorem theorem23_coordinateAscentLoop_total
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (fuel : ℕ) (hbudget : 2 ≤ ((fuel : ℝ) + 1) * epsilon)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial) :
    ∃ output,
      coordinateAscentLoop law current epsilon oracle fuel initial = some output ∧
        EpsilonCoordinatewiseLocal law current G H epsilon output := by
  obtain ⟨output, houtput⟩ := coordinateAscentLoop_terminates_of_budget
    law current epsilon hepsilon oracle fuel hbudget initial
  exact ⟨output, houtput,
    theorem23_coordinateAscentLoop_local law current epsilon oracle fuel
      initial output hinitial houtput⟩

/-- Source-shaped positive-certificate conclusion for the repaired algorithm.
If the arbitrary initial pair in Algorithm 6 is a genuine positive
certificate, coordinate ascent preserves positivity and returns a positive
certificate satisfying the advertised two-sided local guarantee. -/
theorem theorem23_coordinateAscentLoop_positive_certificate
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {G : Set (Group X)} {H : Set (Model X Bool)}
    (oracle : CoordinateBestResponses law current G H)
    (fuel : ℕ) (hbudget : 2 ≤ ((fuel : ℝ) + 1) * epsilon)
    (initial : CertificatePair X) (hinitial : PairAdmissible G H initial)
    (hpositive : 0 < binaryCertificateObjective law current initial.group
      initial.replacement) :
    ∃ output,
      coordinateAscentLoop law current epsilon oracle fuel initial = some output ∧
        EpsilonCoordinatewiseLocal law current G H epsilon output ∧
        CertificateOfSuboptimality law binaryZeroOneLoss current output.group
          output.replacement (groupMass law output.group)
          (groupLoss law binaryZeroOneLoss current output.group -
            groupLoss law binaryZeroOneLoss output.replacement output.group) := by
  obtain ⟨output, houtput, hlocal⟩ := theorem23_coordinateAscentLoop_total
    law current epsilon hepsilon oracle fuel hbudget initial hinitial
  have hmono := coordinateAscentLoop_objective_mono law current epsilon
    hepsilon.le oracle fuel initial output houtput
  have houtputPositive :
      0 < binaryCertificateObjective law current output.group
        output.replacement := lt_of_lt_of_le hpositive hmono
  exact ⟨output, houtput, hlocal,
    canonical_certificate_of_positive_score houtputPositive⟩

/-- A source-shaped sequence of strict epsilon-improving coordinate updates. -/
def ImprovingCoordinateSequence {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool) (epsilon : ℝ) :
    CertificatePair X → List (CertificatePair X) → Prop
  | _, [] => True
  | pair, next :: rest =>
      binaryCertificateObjective law current pair.group pair.replacement + epsilon ≤
          binaryCertificateObjective law current next.group next.replacement ∧
        ImprovingCoordinateSequence law current epsilon next rest

/-- Repeated coordinate improvements accumulate linearly. -/
theorem improvingCoordinateSequence_objective_gain
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool) (epsilon : ℝ)
    (initial : CertificatePair X) (updates : List (CertificatePair X))
    (hsequence : ImprovingCoordinateSequence law current epsilon initial updates) :
    binaryCertificateObjective law current initial.group initial.replacement +
        (updates.length : ℝ) * epsilon ≤
      binaryCertificateObjective law current
        (updates.getLastD initial).group (updates.getLastD initial).replacement := by
  induction updates generalizing initial with
  | nil => simp
  | cons next rest ih =>
      rcases hsequence with ⟨hstep, hrest⟩
      have htail := ih next hrest
      cases rest with
      | nil =>
          simp at htail ⊢
          linarith
      | cons later tail =>
          rw [List.getLastD_cons] at htail
          have htail' :
              binaryCertificateObjective law current next.group next.replacement +
                  ((tail.length : ℝ) + 1) * epsilon ≤
                binaryCertificateObjective law current (tail.getLastD later).group
                  (tail.getLastD later).replacement := by
            simpa [List.length_cons] using htail
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
            List.getLastD_cons]
          nlinarith

/-- Theorem 23 runtime: no epsilon-improving trajectory has over `2/epsilon` updates. -/
theorem theorem23_coordinate_update_bound
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (initial : CertificatePair X) (updates : List (CertificatePair X))
    (hsequence : ImprovingCoordinateSequence law current epsilon initial updates) :
    (updates.length : ℝ) ≤ 2 / epsilon := by
  have hgain := improvingCoordinateSequence_objective_gain law current epsilon
    initial updates hsequence
  have hinitial := binaryCertificateObjective_mem_Icc law current initial
  have hfinal := binaryCertificateObjective_mem_Icc law current (updates.getLastD initial)
  rcases hinitial with ⟨hinitialLower, hinitialUpper⟩
  rcases hfinal with ⟨hfinalLower, hfinalUpper⟩
  apply (le_div_iff₀ hepsilon).2
  nlinarith

/-- A positive local-optimum score is a genuine source certificate. -/
theorem local_pair_certificate_of_positive_objective
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (pair : CertificatePair X)
    (hpositive : 0 < binaryCertificateObjective law current pair.group pair.replacement) :
    CertificateOfSuboptimality law binaryZeroOneLoss current pair.group
      pair.replacement (groupMass law pair.group)
      (groupLoss law binaryZeroOneLoss current pair.group -
        groupLoss law binaryZeroOneLoss pair.replacement pair.group) := by
  exact canonical_certificate_of_positive_score hpositive

/-! ## Printed Theorem 23 defect witness -/

/-- One-point population used to show that coordinatewise local optimality does
not imply the positive-certificate conclusion printed in Theorem 23. -/
def theorem23CounterexampleLaw : Distribution Unit Bool :=
  PMF.pure ((), false)

/-- The Bayes-optimal constant model in the one-point counterexample. -/
def theorem23CounterexampleModel : Model Unit Bool := fun _ => false

/-- The full population group in the one-point counterexample. -/
def theorem23CounterexampleGroup : Group Unit := fun _ => true

/-- The unique candidate pair in the one-point counterexample classes. -/
def theorem23CounterexamplePair : CertificatePair Unit :=
  { group := theorem23CounterexampleGroup
    replacement := theorem23CounterexampleModel }

/-- Printed Theorem 23 is false without a positive-score premise: the unique
pair can be coordinatewise locally optimal for a positive tolerance while no
positive `(mu, Delta)` certificate exists. -/
theorem theorem23_local_optimum_without_positive_certificate :
    EpsilonCoordinatewiseLocal theorem23CounterexampleLaw
        theorem23CounterexampleModel
        ({theorem23CounterexampleGroup} : Set (Group Unit))
        ({theorem23CounterexampleModel} : Set (Model Unit Bool))
        (1 / 2 : ℝ) theorem23CounterexamplePair ∧
      ¬ ∃ mu Delta,
        CertificateOfSuboptimality theorem23CounterexampleLaw binaryZeroOneLoss
          theorem23CounterexampleModel theorem23CounterexampleGroup
          theorem23CounterexampleModel mu Delta := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simp [PairAdmissible, theorem23CounterexamplePair]
    · intro h hh
      have heq : h = theorem23CounterexampleModel := by simpa using hh
      subst h
      simp [theorem23CounterexamplePair]
    · intro g hg
      have heq : g = theorem23CounterexampleGroup := by simpa using hg
      subst g
      simp [theorem23CounterexamplePair]
  · rintro ⟨mu, Delta, hcert⟩
    rcases hcert with ⟨_, hDelta, _, hgap⟩
    linarith

end

end GHKR22BiasBounties

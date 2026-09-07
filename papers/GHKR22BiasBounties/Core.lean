import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Learning.Prediction.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bias-bounty population model and deterministic update core

This file formalizes Definitions 1--7, Observation 4, Theorem 8, Algorithm 1,
and Theorems 9--10 of Globus-Harris, Kearns, and Roth (2022).  The population
law is represented by a finite PMF.  This is an exact model for every empirical
distribution and every finite-support population distribution; all identities
are stated for the paper's arbitrary `[0,1]`-valued loss rather than only for
squared loss.

The paper writes approximate Bayes optimality using a division by group mass.
We use the equivalent mass-weighted inequality as the primitive definition.
This gives the mathematically natural value at a zero-mass group and avoids an
undefined source expression.  `approxBayesOptimal_pair_iff_source` proves the
exact bridge back to the displayed source formula whenever the group has
positive mass.
-/

namespace GHKR22BiasBounties

noncomputable section

open scoped BigOperators

/-- A prediction model maps features to labels. -/
abbrev Model := AppliedModelingLib.Learning.Prediction.Model

/-- A subgroup is a Boolean-valued feature predicate (Definition 1). -/
abbrev Group := AppliedModelingLib.Learning.Prediction.HardGroup

/-- A finite-support joint population law over labelled examples. -/
abbrev Distribution (X Y : Type*) := PMF (X × Y)

/-- A loss function with the paper's normalization `0 ≤ loss ≤ 1`. -/
abbrev BoundedLoss := AppliedModelingLib.Learning.Prediction.BoundedLoss

/-- Real indicator of membership in a Boolean group. -/
abbrev groupIndicator {X : Type*} (g : Group X) (x : X) : ℝ :=
  AppliedModelingLib.Learning.Prediction.hardGroupIndicator g x

/-- Loss of `f` on one labelled example. -/
def datumLoss {X Y : Type*} (loss : BoundedLoss Y) (f : Model X Y)
    (datum : X × Y) : ℝ :=
  loss.value (f datum.1) datum.2

/-- Definition 2: population model loss. -/
def modelLoss {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y) : ℝ :=
  AppliedModelingLib.pmfExp law (datumLoss loss f)

/-- Definition 1: population mass of a group. -/
def groupMass {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (g : Group X) : ℝ :=
  AppliedModelingLib.pmfExp law (fun datum => groupIndicator g datum.1)

/-- Mass-weighted numerator of the conditional group loss. -/
def groupLossNumerator {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) : ℝ :=
  AppliedModelingLib.pmfExp law
    (fun datum => groupIndicator g datum.1 * datumLoss loss f datum)

/-- Definition 2: conditional group loss, totalized to zero at zero mass. -/
def groupLoss {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) : ℝ :=
  groupLossNumerator law loss f g / groupMass law g

/-- The mass-weighted improvement objective used throughout the paper. -/
def certificateImprovementScore {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y) : ℝ :=
  groupMass law g * (groupLoss law loss f g - groupLoss law loss h g)

/-- Definition 5 in mass-weighted form. -/
def ApproxBayesOptimal {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (certificates : Set (Group X × Model X Y))
    (epsilon : ℝ) (f : Model X Y) : Prop :=
  ∀ pair ∈ certificates,
    certificateImprovementScore law loss f pair.1 pair.2 ≤ epsilon

/-- Definition 7, including the source's positive-parameter convention. -/
def CertificateOfSuboptimality {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y)
    (mu Delta : ℝ) : Prop :=
  0 < mu ∧ 0 < Delta ∧
    mu ≤ groupMass law g ∧
    groupLoss law loss h g + Delta ≤ groupLoss law loss f g

/-- The finite pointwise Bayes-risk numerator at feature `x`. -/
def pointwiseRiskNumerator {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (x : X) (prediction : Y) : ℝ :=
  ∑ truth : Y, (law (x, truth)).toReal * loss.value prediction truth

/-- Definition 3: pointwise Bayes optimality on the population support. -/
def BayesOptimal {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y) : Prop :=
  ∀ x prediction,
    pointwiseRiskNumerator law loss x (f x) ≤
      pointwiseRiskNumerator law loss x prediction

/-- Groupwise numerator optimality; this is division-free at zero-mass groups. -/
def GroupwiseOptimal {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y) : Prop :=
  ∀ g h, groupLossNumerator law loss f g ≤ groupLossNumerator law loss h g

/-- Group mass is nonnegative. -/
theorem groupMass_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (g : Group X) :
    0 ≤ groupMass law g := by
  apply AppliedModelingLib.pmfExp_nonneg_of_forall_nonneg
  intro datum
  cases hg : g datum.1 <;> simp [groupIndicator, hg]

/-- Population loss is nonnegative. -/
theorem modelLoss_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y) :
    0 ≤ modelLoss law loss f := by
  apply AppliedModelingLib.pmfExp_nonneg_of_forall_nonneg
  exact fun datum => loss.nonneg _ _

/-- Population loss is at most one. -/
theorem modelLoss_le_one {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y) :
    modelLoss law loss f ≤ 1 := by
  exact AppliedModelingLib.pmfExp_le_of_forall_le law _ 1
    (fun datum => loss.le_one _ _)

/-- A group-loss numerator is nonnegative. -/
theorem groupLossNumerator_nonneg {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) :
    0 ≤ groupLossNumerator law loss f g := by
  apply AppliedModelingLib.pmfExp_nonneg_of_forall_nonneg
  intro datum
  exact mul_nonneg (by cases hg : g datum.1 <;> simp [groupIndicator, hg])
    (loss.nonneg _ _)

/-- A `[0,1]` group-loss numerator is at most the group's mass. -/
theorem groupLossNumerator_le_groupMass {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) :
    groupLossNumerator law loss f g ≤ groupMass law g := by
  apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
  intro datum
  cases hg : g datum.1
  · simp [groupIndicator, hg]
  · simpa [groupIndicator, hg, datumLoss] using loss.le_one (f datum.1) datum.2

/-- Every group-loss numerator vanishes on a zero-mass group. -/
theorem groupLossNumerator_eq_zero_of_groupMass_eq_zero {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X)
    (hmass : groupMass law g = 0) :
    groupLossNumerator law loss f g = 0 := by
  apply le_antisymm
  · simpa [hmass] using groupLossNumerator_le_groupMass law loss f g
  · exact groupLossNumerator_nonneg law loss f g

/-- On a positive-mass group, numerator and conditional loss multiply exactly. -/
theorem groupMass_mul_groupLoss {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X)
    (hmass : groupMass law g ≠ 0) :
    groupMass law g * groupLoss law loss f g =
      groupLossNumerator law loss f g := by
  unfold groupLoss
  field_simp

/-- The weighted score is the difference of group-loss numerators. -/
theorem certificateImprovementScore_eq_numerator_sub {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y)
    (hmass : groupMass law g ≠ 0) :
    certificateImprovementScore law loss f g h =
      groupLossNumerator law loss f g - groupLossNumerator law loss h g := by
  unfold certificateImprovementScore
  rw [mul_sub, groupMass_mul_groupLoss law loss f g hmass,
    groupMass_mul_groupLoss law loss h g hmass]

/-- The weighted score/numerator identity also covers zero-mass groups. -/
theorem certificateImprovementScore_eq_numerator_sub_total {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y) :
    certificateImprovementScore law loss f g h =
      groupLossNumerator law loss f g - groupLossNumerator law loss h g := by
  by_cases hmass : groupMass law g = 0
  · rw [groupLossNumerator_eq_zero_of_groupMass_eq_zero law loss f g hmass,
      groupLossNumerator_eq_zero_of_groupMass_eq_zero law loss h g hmass]
    simp [certificateImprovementScore, hmass]
  · exact certificateImprovementScore_eq_numerator_sub law loss f g h hmass

/-- Definition 5 agrees with the paper's divided formula at positive mass. -/
theorem approxBayesOptimal_pair_iff_source {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (f h : Model X Y) (g : Group X)
    (hmass : 0 < groupMass law g) :
    certificateImprovementScore law loss f g h ≤ epsilon ↔
      groupLoss law loss f g ≤
        groupLoss law loss h g + epsilon / groupMass law g := by
  unfold certificateImprovementScore
  constructor <;> intro hineq
  · have hmul :
        (groupLoss law loss f g - groupLoss law loss h g) *
            groupMass law g ≤ epsilon := by
      nlinarith
    have hgap := (le_div_iff₀ hmass).2 hmul
    linarith
  · have hgap :
        groupLoss law loss f g - groupLoss law loss h g ≤
          epsilon / groupMass law g := by
      linarith
    have hmul := (le_div_iff₀ hmass).1 hgap
    nlinarith

/-- Every positive certificate lower-bounds the weighted improvement score. -/
theorem certificate_mul_le_improvementScore {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y}
    {f : Model X Y} {g : Group X} {h : Model X Y} {mu Delta : ℝ}
    (hcert : CertificateOfSuboptimality law loss f g h mu Delta) :
    mu * Delta ≤ certificateImprovementScore law loss f g h := by
  rcases hcert with ⟨hmu, hDelta, hmass, hgap⟩
  have hgap' : Delta ≤ groupLoss law loss f g - groupLoss law loss h g := by
    linarith
  have hgroupMass : 0 ≤ groupMass law g := groupMass_nonneg law g
  exact mul_le_mul hmass hgap' hDelta.le hgroupMass

/-- A positive weighted score supplies the canonical mass/gap certificate. -/
theorem canonical_certificate_of_positive_score {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y}
    {f : Model X Y} {g : Group X} {h : Model X Y}
    (hscore : 0 < certificateImprovementScore law loss f g h) :
    CertificateOfSuboptimality law loss f g h
      (groupMass law g)
      (groupLoss law loss f g - groupLoss law loss h g) := by
  have hmass_nonneg := groupMass_nonneg law g
  have hmul : 0 < groupMass law g *
      (groupLoss law loss f g - groupLoss law loss h g) := by
    simpa [certificateImprovementScore] using hscore
  have hmass_pos : 0 < groupMass law g := by
    by_contra hnot
    have hzero : groupMass law g = 0 := le_antisymm (le_of_not_gt hnot) hmass_nonneg
    simp [hzero] at hmul
  have hgap_pos : 0 < groupLoss law loss f g - groupLoss law loss h g :=
    by
      rcases mul_pos_iff.mp hmul with hpositive | hnegative
      · exact hpositive.2
      · exact False.elim ((not_lt_of_ge hmass_nonneg) hnegative.1)
  refine ⟨hmass_pos, hgap_pos, le_rfl, ?_⟩
  linarith

/-!
## Observation 4
-/

/-- Pointwise Bayes optimality implies optimality on every subgroup. -/
theorem groupwiseOptimal_of_bayesOptimal {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y} {f : Model X Y}
    (hbayes : BayesOptimal law loss f) :
    GroupwiseOptimal law loss f := by
  intro g h
  unfold groupLossNumerator AppliedModelingLib.pmfExp datumLoss groupIndicator
    AppliedModelingLib.Learning.Prediction.hardGroupIndicator
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro x _
  by_cases hg : g x
  · simp only [hg, ↓reduceIte, one_mul]
    exact hbayes x (h x)
  · simp [hg]

/-- Optimality on every subgroup implies pointwise Bayes optimality. -/
theorem bayesOptimal_of_groupwiseOptimal {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y} {f : Model X Y}
    (hgroups : GroupwiseOptimal law loss f) :
    BayesOptimal law loss f := by
  intro x prediction
  let singleton : Group X := fun x' => decide (x' = x)
  let replacement : Model X Y := fun x' => if x' = x then prediction else f x'
  have h := hgroups singleton replacement
  unfold groupLossNumerator AppliedModelingLib.pmfExp datumLoss groupIndicator
    AppliedModelingLib.Learning.Prediction.hardGroupIndicator at h
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have hcollapse (m : Model X Y) :
      (∑ x' : X, ∑ truth : Y,
          (law (x', truth)).toReal *
            ((if singleton x' then 1 else 0) * loss.value (m x') truth)) =
        ∑ truth : Y, (law (x, truth)).toReal * loss.value (m x) truth := by
    classical
    let contribution : X → ℝ := fun x' =>
      ∑ truth : Y,
        (law (x', truth)).toReal *
          ((if singleton x' then 1 else 0) * loss.value (m x') truth)
    calc
      (∑ x' : X, ∑ truth : Y,
          (law (x', truth)).toReal *
            ((if singleton x' then 1 else 0) * loss.value (m x') truth)) =
          contribution x := by
            apply Finset.sum_eq_single x
            · intro x' _ hxx
              simp [contribution, singleton, hxx]
            · simp
      _ = ∑ truth : Y,
          (law (x, truth)).toReal * loss.value (m x) truth := by
            simp [contribution, singleton]
  rw [hcollapse f, hcollapse replacement] at h
  simpa [pointwiseRiskNumerator, replacement] using h

/-- Observation 4, in the division-free groupwise form. -/
theorem observation4_bayesOptimal_iff_groupwiseOptimal {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (f : Model X Y) :
    BayesOptimal law loss f ↔ GroupwiseOptimal law loss f := by
  exact ⟨groupwiseOptimal_of_bayesOptimal, bayesOptimal_of_groupwiseOptimal⟩

/-!
## Theorem 8
-/

/-- Theorem 8: large certificates are equivalent to failure of approximation. -/
theorem theorem8_certificate_iff_not_approxBayesOptimal {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (certificates : Set (Group X × Model X Y))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (f : Model X Y) :
    (∃ g h mu Delta,
        (g, h) ∈ certificates ∧
        CertificateOfSuboptimality law loss f g h mu Delta ∧
        epsilon < mu * Delta) ↔
      ¬ ApproxBayesOptimal law loss certificates epsilon f := by
  constructor
  · rintro ⟨g, h, mu, Delta, hmem, hcert, hlarge⟩ happ
    have hbound := happ (g, h) hmem
    have hmul := certificate_mul_le_improvementScore hcert
    linarith
  · intro hnot
    unfold ApproxBayesOptimal at hnot
    push_neg at hnot
    rcases hnot with ⟨pair, hmem, hscore⟩
    have hpositive : 0 < certificateImprovementScore law loss f pair.1 pair.2 :=
      lt_of_le_of_lt hepsilon hscore
    refine ⟨pair.1, pair.2, groupMass law pair.1,
      groupLoss law loss f pair.1 - groupLoss law loss pair.2 pair.1,
      hmem, canonical_certificate_of_positive_score hpositive, ?_⟩
    simpa [certificateImprovementScore] using hscore

/-!
## Algorithm 1 and Theorems 9--10
-/

/-- Algorithm 1: use `h` on the submitted group and `f` elsewhere. -/
def listUpdate {X Y : Type*} (f : Model X Y) (g : Group X)
    (h : Model X Y) : Model X Y :=
  fun x => if g x then h x else f x

/-- Algorithm 1 agrees with `h` on the submitted group. -/
@[simp] theorem listUpdate_eq_on_group {X Y : Type*}
    (f : Model X Y) (g : Group X) (h : Model X Y)
    {x : X} (hx : g x = true) :
    listUpdate f g h x = h x := by
  simp [listUpdate, hx]

/-- Algorithm 1 agrees with `f` outside the submitted group. -/
@[simp] theorem listUpdate_eq_off_group {X Y : Type*}
    (f : Model X Y) (g : Group X) (h : Model X Y)
    {x : X} (hx : g x = false) :
    listUpdate f g h x = f x := by
  simp [listUpdate, hx]

/-- The updated model has exactly the submitted model's group loss numerator. -/
theorem listUpdate_groupLossNumerator_eq {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y) :
    groupLossNumerator law loss (listUpdate f g h) g =
      groupLossNumerator law loss h g := by
  unfold groupLossNumerator
  apply AppliedModelingLib.pmfExp_congr
  intro datum
  cases hg : g datum.1 <;> simp [groupIndicator, listUpdate, datumLoss, hg]

/-- Therefore the updated model exactly matches `h`'s conditional group loss. -/
theorem listUpdate_groupLoss_eq {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y) :
    groupLoss law loss (listUpdate f g h) g = groupLoss law loss h g := by
  simp [groupLoss, listUpdate_groupLossNumerator_eq]

/-- Exact total-loss change under `ListUpdate`. -/
theorem modelLoss_sub_listUpdate_eq_numerator_sub {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (f : Model X Y) (g : Group X) (h : Model X Y) :
    modelLoss law loss f - modelLoss law loss (listUpdate f g h) =
      groupLossNumerator law loss f g - groupLossNumerator law loss h g := by
  unfold modelLoss groupLossNumerator
  rw [← AppliedModelingLib.pmfExp_sub, ← AppliedModelingLib.pmfExp_sub]
  apply AppliedModelingLib.pmfExp_congr
  intro datum
  cases hg : g datum.1 <;>
    simp [datumLoss, groupIndicator, listUpdate, hg]

/-- Theorem 9: exact repair and at least `mu * Delta` total-loss progress. -/
theorem theorem9_listUpdate_progress {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {law : Distribution X Y} {loss : BoundedLoss Y}
    {f : Model X Y} {g : Group X} {h : Model X Y} {mu Delta : ℝ}
    (hcert : CertificateOfSuboptimality law loss f g h mu Delta) :
    groupLoss law loss (listUpdate f g h) g = groupLoss law loss h g ∧
      modelLoss law loss (listUpdate f g h) ≤
        modelLoss law loss f - mu * Delta := by
  refine ⟨listUpdate_groupLoss_eq law loss f g h, ?_⟩
  have hmass_ne : groupMass law g ≠ 0 := ne_of_gt (lt_of_lt_of_le hcert.1 hcert.2.2.1)
  have hscore := certificate_mul_le_improvementScore hcert
  rw [certificateImprovementScore_eq_numerator_sub law loss f g h hmass_ne] at hscore
  rw [← modelLoss_sub_listUpdate_eq_numerator_sub law loss f g h] at hscore
  linarith

/-- One source-shaped update record. -/
structure Update (X Y : Type*) where
  group : Group X
  replacement : Model X Y
  mu : ℝ
  Delta : ℝ

/-- Sequential decision-list semantics for a list of updates. -/
def runUpdates {X Y : Type*} (initial : Model X Y) :
    List (Update X Y) → Model X Y
  | [] => initial
  | update :: rest =>
      runUpdates (listUpdate initial update.group update.replacement) rest

/-- Every update is a large valid certificate for the model then in force. -/
def ValidUpdateSequence {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ) :
    Model X Y → List (Update X Y) → Prop
  | _, [] => True
  | current, update :: rest =>
      CertificateOfSuboptimality law loss current update.group
          update.replacement update.mu update.Delta ∧
        epsilon ≤ update.mu * update.Delta ∧
        ValidUpdateSequence law loss epsilon
          (listUpdate current update.group update.replacement) rest

/-- Repeated valid updates lower loss by at least `length * epsilon`. -/
theorem runUpdates_loss_le {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (initial : Model X Y) (updates : List (Update X Y))
    (hvalid : ValidUpdateSequence law loss epsilon initial updates) :
    modelLoss law loss (runUpdates initial updates) ≤
      modelLoss law loss initial - (updates.length : ℝ) * epsilon := by
  induction updates generalizing initial with
  | nil => simp [runUpdates]
  | cons update rest ih =>
      rcases hvalid with ⟨hcert, hlarge, hrest⟩
      have hstep := (theorem9_listUpdate_progress hcert).2
      have htail := ih (listUpdate initial update.group update.replacement) hrest
      simp only [runUpdates, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        modelLoss law loss
            (runUpdates (listUpdate initial update.group update.replacement) rest) ≤
            modelLoss law loss (listUpdate initial update.group update.replacement) -
              (rest.length : ℝ) * epsilon := htail
        _ ≤ (modelLoss law loss initial - update.mu * update.Delta) -
              (rest.length : ℝ) * epsilon := sub_le_sub_right hstep _
        _ ≤ modelLoss law loss initial -
              ((rest.length : ℝ) + 1) * epsilon := by
            nlinarith

/-- Theorem 10, multiplication form: `T * epsilon ≤ initial loss ≤ 1`. -/
theorem theorem10_update_bound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (initial : Model X Y) (updates : List (Update X Y))
    (hvalid : ValidUpdateSequence law loss epsilon initial updates) :
    (updates.length : ℝ) * epsilon ≤ modelLoss law loss initial ∧
      modelLoss law loss initial ≤ 1 := by
  have hprogress := runUpdates_loss_le law loss epsilon initial updates hvalid
  have hnonneg := modelLoss_nonneg law loss (runUpdates initial updates)
  constructor
  · linarith
  · exact modelLoss_le_one law loss initial

/-- The displayed division form `T ≤ ell₀ / epsilon` for positive epsilon. -/
theorem theorem10_update_count_le_loss_div {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (initial : Model X Y) (updates : List (Update X Y))
    (hvalid : ValidUpdateSequence law loss epsilon initial updates) :
    (updates.length : ℝ) ≤ modelLoss law loss initial / epsilon ∧
      modelLoss law loss initial / epsilon ≤ 1 / epsilon := by
  have hbound := theorem10_update_bound law loss epsilon initial updates hvalid
  constructor
  · exact (le_div_iff₀ hepsilon).2 hbound.1
  · exact (div_le_div_iff_of_pos_right hepsilon).2 hbound.2

end

end GHKR22BiasBounties

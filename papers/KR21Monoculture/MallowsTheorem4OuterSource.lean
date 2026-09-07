import KR21Monoculture.MallowsDefinition1
import KR21Monoculture.MallowsOuterSource

/-!
# Source-facing outer-D bridge for KR21 Theorem 4

Section 4 of KR21 states its Mallows sequential-choice result after the model
has introduced a joint candidate-value distribution `D`.  The original
fixed-value sequential development proves the finite Mallows comparison for
each value profile.  This module makes the missing ex-ante layer explicit:
at every feasible history, the next firm's payoff is the expectation over
`D` of the finite ranking expectation on the remaining candidate set.

The source labels candidates in strict true-value order before writing its
Mallows law.  Accordingly, the outer theorem below requires that one fixed
center orders the value profile almost everywhere.  This is the visible
rank-labelled interpretation of the source's `x_1 > ... > x_n` convention;
the theorem does not silently sort an arbitrarily identity-labelled `D`.

Coordinatewise integrability is the only analytic condition needed to
interchange the finite ranking expectation and the outer expectation.  The
strict half additionally uses almost-everywhere strict value order, exactly
where strict uniqueness needs it.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter

namespace KR21Monoculture

namespace SourceMallowsSequential

/-- The ex-ante expected payoff from taking the best candidate in a fixed
remaining set under a ranking law independent of the realized value profile. -/
noncomputable def outerExpectedBestInSet {n : ℕ}
    (D : Measure (ValueProfile n)) (law : PMF (Ranking n))
    (remaining : Finset (Candidate n)) : ℝ :=
  DistributionalAccuracyFamily.outerExpected D
    (fun value => expectedBestInSet law value remaining)

/-- The ranking law a sequential firm receives under its selected strategy. -/
def rankingLaw {n : ℕ} (algorithm human : MallowsSpec n) : Strategy → PMF (Ranking n)
  | .algorithm => algorithm.law
  | .human => human.law

/-- The source's ex-ante next-firm payoff after a history of already-hired
candidates.  The remaining set is computed before the next independent ranking
draw, as in the paper's sequential discussion. -/
noncomputable def stepUtility {n : ℕ}
    (D : Measure (ValueProfile n)) (algorithm human : MallowsSpec n)
    (strategy : Strategy) (hired : Finset (Candidate n)) : ℝ :=
  outerExpectedBestInSet D (rankingLaw algorithm human strategy)
    (SequentialModel.remainingAfter hired)

/-- Ex-ante sequential optimality of the all-human sequence.  Only feasible
histories are compared, so the statement does not invent a payoff after every
candidate has been hired. -/
def AllHumanOptimal {n : ℕ}
    (D : Measure (ValueProfile n)) (algorithm human : MallowsSpec n)
    (k : ℕ) : Prop :=
  ∀ i : Fin k, i.val < Fintype.card (Candidate n) →
    ∀ hired : Finset (Candidate n), hired.card = i.val →
      ∀ strategy : Strategy,
        stepUtility D algorithm human strategy hired ≤
          stepUtility D algorithm human Strategy.human hired

/-- Ex-ante strict human optimality at every history with at least two
remaining candidates.  This is the source's meaningful strict-uniqueness
form: with one candidate left, strategy cannot affect the hire. -/
def HumanUniqueAtAllNonterminalHistories {n : ℕ}
    (D : Measure (ValueProfile n)) (algorithm human : MallowsSpec n)
    (k : ℕ) : Prop :=
  ∀ i : Fin k, i.val + 1 < Fintype.card (Candidate n) →
    ∀ hired : Finset (Candidate n), hired.card = i.val →
      ∀ strategy : Strategy,
        (∀ alternative : Strategy,
          stepUtility D algorithm human alternative hired ≤
            stepUtility D algorithm human strategy hired) →
          strategy = Strategy.human

/-- Coordinatewise first moments make the ex-ante best-in-set payoff
integrable for any finite ranking PMF. -/
theorem outerExpectedBestInSet_integrable
    {n : ℕ} (D : Measure (ValueProfile n)) (law : PMF (Ranking n))
    (remaining : Finset (Candidate n))
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable (fun value => expectedBestInSet law value remaining) D := by
  simpa [expectedBestInSet] using
    (integrable_pmfExp_valueSelection D law
      (fun ranking : Ranking n => bestInSet ranking remaining) hvalue)

/-- Pointwise Mallows remaining-set dominance lifts to the source's outer
candidate-value distribution.  The fixed-center a.e. hypothesis is semantic:
it is what lets the finite Mallows law remain independent of the cardinal
profile while preserving the source's true-value ordering. -/
theorem outerExpectedBestInSet_le_of_mallows_q_le
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (horder : ∀ᵐ value ∂D, WeaklyOrderedBy human.center value)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty) :
    outerExpectedBestInSet D algorithm.law remaining ≤
      outerExpectedBestInSet D human.law remaining := by
  unfold outerExpectedBestInSet DistributionalAccuracyFamily.outerExpected
  apply integral_mono_ae
  · exact outerExpectedBestInSet_integrable D algorithm.law remaining hvalue
  · exact outerExpectedBestInSet_integrable D human.law remaining hvalue
  filter_upwards [horder] with value hvalue_ordered
  exact MallowsComparison.paper_theorem4_mallows_remaining_utility_dominance_of_q_le
    hcenter hq_le hvalue_ordered hremaining

/-- The strict pointwise Mallows comparison likewise lifts to an outer source
law, provided the source's strict rank-labelled value order holds almost
everywhere. -/
theorem outerExpectedBestInSet_lt_of_mallows_q_lt
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_lt : human.q < algorithm.q)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy human.center value)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    (hcard : 1 < remaining.card) :
    outerExpectedBestInSet D algorithm.law remaining <
      outerExpectedBestInSet D human.law remaining := by
  unfold outerExpectedBestInSet DistributionalAccuracyFamily.outerExpected
  apply integral_lt_integral_of_ae_lt
  · exact outerExpectedBestInSet_integrable D algorithm.law remaining hvalue
  · exact outerExpectedBestInSet_integrable D human.law remaining hvalue
  filter_upwards [hstrict] with value hvalue_ordered
  exact MallowsComparison.paper_theorem4_mallows_remaining_strict_utility_dominance_of_q_lt
    hcenter hq_lt hvalue_ordered hremaining hcard

/-- Outer remaining-set dominance supplies all ex-ante sequential best
responses. -/
theorem allHumanOptimal_of_outerRemainingDominance
    {n k : ℕ} (D : Measure (ValueProfile n))
    (algorithm human : MallowsSpec n)
    (hdom : ∀ remaining : Finset (Candidate n), remaining.Nonempty →
      outerExpectedBestInSet D algorithm.law remaining ≤
        outerExpectedBestInSet D human.law remaining) :
    AllHumanOptimal D algorithm human k := by
  intro i hi hired hhired strategy
  cases strategy with
  | algorithm =>
      exact hdom (SequentialModel.remainingAfter hired)
        (SequentialModel.remainingAfter_nonempty_of_card_lt (n := n)
          (by simpa [hhired] using hi))
  | human =>
      exact le_rfl

/-- Outer strict remaining-set dominance makes human the unique ex-ante best
response at every nonterminal history. -/
theorem humanUniqueAtAllNonterminalHistories_of_outerRemainingDominance
    {n k : ℕ} (D : Measure (ValueProfile n))
    (algorithm human : MallowsSpec n)
    (hdom : ∀ remaining : Finset (Candidate n), remaining.Nonempty →
      1 < remaining.card →
        outerExpectedBestInSet D algorithm.law remaining <
          outerExpectedBestInSet D human.law remaining) :
    HumanUniqueAtAllNonterminalHistories D algorithm human k := by
  intro i hi hired hhired strategy hbest
  cases strategy with
  | human => rfl
  | algorithm =>
      have hremaining : (SequentialModel.remainingAfter (n := n) hired).Nonempty :=
        SequentialModel.remainingAfter_nonempty_of_card_lt (n := n)
          (by
            have : hired.card < Fintype.card (Candidate n) := by
              omega
            exact this)
      have hcard : 1 < (SequentialModel.remainingAfter (n := n) hired).card :=
        SequentialModel.remainingAfter_card_gt_one_of_card_succ_lt (n := n)
          (by simpa [hhired] using hi)
      have hle := hbest Strategy.human
      change
        outerExpectedBestInSet D human.law (SequentialModel.remainingAfter hired) ≤
          outerExpectedBestInSet D algorithm.law (SequentialModel.remainingAfter hired) at hle
      have hlt := hdom (SequentialModel.remainingAfter hired) hremaining hcard
      exact False.elim (by linarith)

/-- The concrete source Mallows law at paper parameter `phi`.  The source
writes mass proportional to `phi^(-d)`; locally this is the inverse parameter
`q = phi^-1` at accuracy `theta = phi - 1`. -/
noncomputable def sourceMallowsSpec {n : ℕ}
    (center : Ranking n) (phi : ℝ) : MallowsSpec n :=
  concreteMallowsSpec center (phi - 1)

/-- The concrete source-law parameter is exactly the inverse parameter in the
published Mallows mass formula on its stated domain `phi > 1`. -/
theorem sourceMallowsSpec_q_eq_inv
    {n : ℕ} (center : Ranking n) {phi : ℝ} (hphi : 1 < phi) :
    (sourceMallowsSpec center phi).q = phi⁻¹ := by
  change mallowsAccuracyQ (phi - 1) = phi⁻¹
  rw [mallowsAccuracyQ_eq_of_pos (by linarith)]
  unfold mallowsInverseAccuracyQ
  ring

/-- Source Theorem 4, weak/existence half, with its outer candidate
distribution restored.  If `phi_H >= phi_A > 1`, then every feasible
sequential history has an ex-ante human best response, hence all humans is an
optimal sequence.  The result is robust to every outer law satisfying the
visible rank-labelled and first-moment source regularity conditions. -/
theorem source_theorem4_mallows_outer_allHumanOptimal
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {phiA phiH : ℝ}
    (hphiA : 1 < phiA) (hphiH : 1 < phiH) (haccuracy : phiA ≤ phiH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (horder : ∀ᵐ value ∂D, WeaklyOrderedBy center value) :
    AllHumanOptimal D (sourceMallowsSpec center phiA)
      (sourceMallowsSpec center phiH) k := by
  apply allHumanOptimal_of_outerRemainingDominance D
  intro remaining hremaining
  refine outerExpectedBestInSet_le_of_mallows_q_le
    (human := sourceMallowsSpec center phiH)
    (algorithm := sourceMallowsSpec center phiA)
    D rfl ?_ hvalue horder hremaining
  rw [sourceMallowsSpec_q_eq_inv center hphiH,
    sourceMallowsSpec_q_eq_inv center hphiA]
  exact (inv_le_inv₀ (by linarith) (by linarith)).2 haccuracy

/-- Source Theorem 4, strict/unique half.  The strict source accuracy gap and
almost-everywhere strict true-value order give strict ex-ante dominance at
every history with at least two candidates left. -/
theorem source_theorem4_mallows_outer_humanUnique
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {phiA phiH : ℝ}
    (hphiA : 1 < phiA) (hphiH : 1 < phiH) (haccuracy : phiA < phiH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    HumanUniqueAtAllNonterminalHistories D (sourceMallowsSpec center phiA)
      (sourceMallowsSpec center phiH) k := by
  apply humanUniqueAtAllNonterminalHistories_of_outerRemainingDominance D
  intro remaining hremaining hcard
  refine outerExpectedBestInSet_lt_of_mallows_q_lt
    (human := sourceMallowsSpec center phiH)
    (algorithm := sourceMallowsSpec center phiA)
    D rfl ?_ hvalue hstrict hremaining hcard
  rw [sourceMallowsSpec_q_eq_inv center hphiH,
    sourceMallowsSpec_q_eq_inv center hphiA]
  exact (inv_lt_inv₀ (by linarith) (by linarith)).2 haccuracy

end SourceMallowsSequential

end KR21Monoculture

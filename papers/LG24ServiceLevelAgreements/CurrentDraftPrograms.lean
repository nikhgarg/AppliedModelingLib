import LG24ServiceLevelAgreements.CurrentDraftComplete
import LG24ServiceLevelAgreements.ProposedOptimization

/-!
# Corrected finite current-paper programs

This module states the current manuscript's original joint SLA/GPS/budget
program and its reciprocal-slack reformulation as actual finite feasible sets.
It proves both directions of the corrected change of variables and equality of
their attained optimal values for every coordinatewise nondecreasing loss.
For a convex loss, it also proves convexity of the reciprocal objective along
positive slack vectors.  Thus the optimization result is not packaged as a
candidate-specific lower-bound certificate.

The final section strengthens the corrected Proposition 2.6 from two Boroughs
to arbitrary nontrivial finite Borough and category sets.  Strictness follows
from positive risk-weighted load in every Borough-category cell; the singleton
boundary remains excluded, as required by the counterexample in
`CurrentDraftComplete.lean`.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## The original and corrected reformulated joint programs -/

/-- Decision variables in the manuscript's original joint program. -/
structure OriginalProgramDecision (Borough Category : Type*) where
  delay : Borough → Category → ℝ
  gpsWeight : Borough → Category → ℝ
  boroughCapacity : Borough → ℝ

/-- Decision variables in the corrected reciprocal-slack program. -/
structure ReformulatedProgramDecision (Borough Category : Type*) where
  slack : Borough → Category → ℝ
  boroughCapacity : Borough → ℝ

/-- The source-shaped feasible set of the original SLA/GPS/budget program. -/
structure OriginalProgramFeasible
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    (logTail totalCapacity : ℝ)
    (arrivalRate : Borough → Category → ℝ)
    (d : OriginalProgramDecision Borough Category) : Prop where
  delay_nonneg : ∀ b k, 0 ≤ d.delay b k
  gpsWeight_nonneg : ∀ b k, 0 ≤ d.gpsWeight b k
  capacity_nonneg : ∀ b, 0 ≤ d.boroughCapacity b
  sla : ∀ b k,
    multiplicativeSLAConstraint
      (gpsSlack (d.boroughCapacity b) (d.gpsWeight b k) (arrivalRate b k))
      (d.delay b k) logTail
  gps : ∀ b, ∑ k, d.gpsWeight b k ≤ 1
  budget : ∑ b, d.boroughCapacity b ≤ totalCapacity

/-- The corrected finite reciprocal-slack feasible set.  Strict positivity of
`x` is essential: the reciprocal objective is undefined at the printed
non-strict boundary `x = 0`. -/
structure ReformulatedProgramFeasible
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    (totalCapacity : ℝ)
    (arrivalRate : Borough → Category → ℝ)
    (d : ReformulatedProgramDecision Borough Category) : Prop where
  slack_pos : ∀ b k, 0 < d.slack b k
  capacity_nonneg : ∀ b, 0 ≤ d.boroughCapacity b
  borough_slack : ∀ b,
    ∑ k, d.slack b k ≤
      d.boroughCapacity b - ∑ k, arrivalRate b k
  budget : ∑ b, d.boroughCapacity b ≤ totalCapacity

/-- Substitute each original guaranteed service slack for `x`. -/
def originalToReformulated
    {Borough Category : Type*}
    (arrivalRate : Borough → Category → ℝ)
    (d : OriginalProgramDecision Borough Category) :
    ReformulatedProgramDecision Borough Category where
  slack b k :=
    gpsSlack (d.boroughCapacity b) (d.gpsWeight b k) (arrivalRate b k)
  boroughCapacity := d.boroughCapacity

/-- Recover binding delays and the corrected GPS weights
`phi = (x + lambda) / C_b`. -/
def reformulatedToOriginal
    {Borough Category : Type*}
    (logTail : ℝ) (arrivalRate : Borough → Category → ℝ)
    (d : ReformulatedProgramDecision Borough Category) :
    OriginalProgramDecision Borough Category where
  delay b k := bindingSLADelay logTail (d.slack b k)
  gpsWeight b k :=
    reconstructedWeight (d.slack b) (arrivalRate b) (d.boroughCapacity b) k
  boroughCapacity := d.boroughCapacity

/-- Every feasible original decision induces a feasible corrected slack
decision, with positivity derived from the SLA rather than assumed separately. -/
theorem originalToReformulated_feasible
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    {logTail totalCapacity : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {d : OriginalProgramDecision Borough Category}
    (hlogTail : 0 < logTail)
    (hd : OriginalProgramFeasible logTail totalCapacity arrivalRate d) :
    ReformulatedProgramFeasible totalCapacity arrivalRate
      (originalToReformulated arrivalRate d) := by
  classical
  refine
    { slack_pos := ?_
      capacity_nonneg := hd.capacity_nonneg
      borough_slack := ?_
      budget := hd.budget }
  · intro b k
    exact finiteSLA_requires_positive_slack
      (hd.delay_nonneg b k) hlogTail (hd.sla b k)
  · intro b
    change
      ∑ k, gpsSlack (d.boroughCapacity b) (d.gpsWeight b k)
          (arrivalRate b k) ≤
        d.boroughCapacity b - ∑ k, arrivalRate b k
    calc
      ∑ k, gpsSlack (d.boroughCapacity b) (d.gpsWeight b k)
          (arrivalRate b k) =
          d.boroughCapacity b * (∑ k, d.gpsWeight b k) -
            ∑ k, arrivalRate b k := by
              simp_rw [gpsSlack, Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ d.boroughCapacity b * 1 - ∑ k, arrivalRate b k := by
        exact sub_le_sub_right
          (mul_le_mul_of_nonneg_left (hd.gps b) (hd.capacity_nonneg b)) _
      _ = d.boroughCapacity b - ∑ k, arrivalRate b k := by ring

/-- Positive reformulated slacks and nonnegative arrivals force every Borough
capacity to be strictly positive; no extra denominator certificate is needed. -/
theorem reformulatedProgram_capacity_pos
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {totalCapacity : ℝ} {arrivalRate : Borough → Category → ℝ}
    {d : ReformulatedProgramDecision Borough Category}
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hd : ReformulatedProgramFeasible totalCapacity arrivalRate d) :
    ∀ b, 0 < d.boroughCapacity b := by
  intro b
  have hxsum : 0 < ∑ k, d.slack b k :=
    Finset.sum_pos (fun k _hk ↦ hd.slack_pos b k) Finset.univ_nonempty
  have halsum : 0 ≤ ∑ k, arrivalRate b k :=
    Finset.sum_nonneg (fun k _hk ↦ harrival b k)
  have haggregate := hd.borough_slack b
  linarith

/-- Every corrected reformulated feasible point recovers a feasible point of
the original joint program, with every SLA constraint binding. -/
theorem reformulatedToOriginal_feasible
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {logTail totalCapacity : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {d : ReformulatedProgramDecision Borough Category}
    (hlogTail : 0 < logTail)
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hd : ReformulatedProgramFeasible totalCapacity arrivalRate d) :
    OriginalProgramFeasible logTail totalCapacity arrivalRate
      (reformulatedToOriginal logTail arrivalRate d) := by
  classical
  have hcapacity : ∀ b, 0 < d.boroughCapacity b :=
    reformulatedProgram_capacity_pos harrival hd
  refine
    { delay_nonneg := ?_
      gpsWeight_nonneg := ?_
      capacity_nonneg := hd.capacity_nonneg
      sla := ?_
      gps := ?_
      budget := hd.budget }
  · intro b k
    exact (div_pos hlogTail (hd.slack_pos b k)).le
  · intro b k
    unfold reformulatedToOriginal reconstructedWeight
    exact div_nonneg
      (add_nonneg (hd.slack_pos b k).le (harrival b k))
      (hcapacity b).le
  · intro b k
    have hrecovery := reconstructedWeight_recovers_slack
      (x := d.slack b) (arrivalRate := arrivalRate b)
      (hcapacity b).ne' k
    change multiplicativeSLAConstraint
      (gpsSlack (d.boroughCapacity b)
        (reconstructedWeight (d.slack b) (arrivalRate b)
          (d.boroughCapacity b) k)
        (arrivalRate b k))
      (bindingSLADelay logTail (d.slack b k)) logTail
    rw [hrecovery]
    unfold multiplicativeSLAConstraint
    rw [bindingSLADelay_mul_slack (hd.slack_pos b k).ne']
  · intro b
    change
      ∑ k, reconstructedWeight (d.slack b) (arrivalRate b)
        (d.boroughCapacity b) k ≤ 1
    exact (reconstructedWeight_sum_le_one_iff
      Finset.univ (d.slack b) (arrivalRate b) (hcapacity b)).2
      (hd.borough_slack b)

/-- A loss is nondecreasing in every SLA coordinate. -/
def CoordinatewiseNondecreasing
    {Borough Category : Type*}
    (loss : (Borough → Category → ℝ) → ℝ) : Prop :=
  ∀ ⦃x y⦄, (∀ b k, x b k ≤ y b k) → loss x ≤ loss y

/-- A direct finite-dimensional convexity predicate for a loss. -/
def CoordinatewiseConvex
    {Borough Category : Type*}
    (loss : (Borough → Category → ℝ) → ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 → ∀ x y,
    loss (fun b k ↦ t * x b k + (1 - t) * y b k) ≤
      t * loss x + (1 - t) * loss y

/-- The exact pair of objective assumptions stated in the current manuscript. -/
structure ConvexNondecreasingLoss
    {Borough Category : Type*}
    (loss : (Borough → Category → ℝ) → ℝ) : Prop where
  nondecreasing : CoordinatewiseNondecreasing loss
  convex : CoordinatewiseConvex loss

/-- Original and corrected reformulated objective functions. -/
def originalProgramObjective
    {Borough Category : Type*}
    (loss : (Borough → Category → ℝ) → ℝ)
    (d : OriginalProgramDecision Borough Category) : ℝ :=
  loss d.delay

def reformulatedProgramObjective
    {Borough Category : Type*}
    (logTail : ℝ) (loss : (Borough → Category → ℝ) → ℝ)
    (d : ReformulatedProgramDecision Borough Category) : ℝ :=
  loss (fun b k ↦ bindingSLADelay logTail (d.slack b k))

/-- Tightening every feasible SLA to its binding reciprocal delay weakly
improves any coordinatewise nondecreasing loss. -/
theorem original_binding_tightening_objective_le_of_pos
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    {logTail totalCapacity : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {loss : (Borough → Category → ℝ) → ℝ}
    {d : OriginalProgramDecision Borough Category}
    (hlogTail : 0 < logTail)
    (hmono : CoordinatewiseNondecreasing loss)
    (hd : OriginalProgramFeasible logTail totalCapacity arrivalRate d) :
    reformulatedProgramObjective logTail loss
        (originalToReformulated arrivalRate d) ≤
      originalProgramObjective loss d := by
  apply hmono
  intro b k
  exact bindingSLADelay_le_of_feasible
    (finiteSLA_requires_positive_slack
      (hd.delay_nonneg b k) hlogTail (hd.sla b k))
    (hd.sla b k)

/-- An optimizer of the corrected reciprocal program recovers an optimizer of
the original joint program. -/
theorem reformulated_minimizer_recovers_original_minimizer
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {logTail totalCapacity : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {loss : (Borough → Category → ℝ) → ℝ}
    {d : ReformulatedProgramDecision Borough Category}
    (hlogTail : 0 < logTail)
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hmono : CoordinatewiseNondecreasing loss)
    (hd : AppliedModelingLib.Optimization.IsMinimizerOn
      (ReformulatedProgramFeasible totalCapacity arrivalRate)
      (reformulatedProgramObjective logTail loss) d) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (OriginalProgramFeasible logTail totalCapacity arrivalRate)
      (originalProgramObjective loss)
      (reformulatedToOriginal logTail arrivalRate d) := by
  constructor
  · exact reformulatedToOriginal_feasible hlogTail harrival hd.1
  · intro candidate hcandidate
    have href := originalToReformulated_feasible hlogTail hcandidate
    have hopt := hd.2 (originalToReformulated arrivalRate candidate) href
    exact hopt.trans
      (original_binding_tightening_objective_le_of_pos
        hlogTail hmono hcandidate)

/-- An optimizer of the original program maps to an optimizer of the corrected
reciprocal program.  Flat losses are allowed: binding is proved to have the
same optimal value, not falsely asserted to be the unique original solution. -/
theorem original_minimizer_maps_to_reformulated_minimizer
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {logTail totalCapacity : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {loss : (Borough → Category → ℝ) → ℝ}
    {d : OriginalProgramDecision Borough Category}
    (hlogTail : 0 < logTail)
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hmono : CoordinatewiseNondecreasing loss)
    (hd : AppliedModelingLib.Optimization.IsMinimizerOn
      (OriginalProgramFeasible logTail totalCapacity arrivalRate)
      (originalProgramObjective loss) d) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (ReformulatedProgramFeasible totalCapacity arrivalRate)
      (reformulatedProgramObjective logTail loss)
      (originalToReformulated arrivalRate d) := by
  constructor
  · exact originalToReformulated_feasible hlogTail hd.1
  · intro candidate hcandidate
    have horiginal := reformulatedToOriginal_feasible
      hlogTail harrival hcandidate
    exact (original_binding_tightening_objective_le_of_pos
      hlogTail hmono hd.1).trans (hd.2 _ horiginal)

/-- At an original optimum, reciprocal binding preserves the objective value. -/
theorem original_minimizer_binding_value_eq
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {logTail totalCapacity : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {loss : (Borough → Category → ℝ) → ℝ}
    {d : OriginalProgramDecision Borough Category}
    (hlogTail : 0 < logTail)
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hmono : CoordinatewiseNondecreasing loss)
    (hd : AppliedModelingLib.Optimization.IsMinimizerOn
      (OriginalProgramFeasible logTail totalCapacity arrivalRate)
      (originalProgramObjective loss) d) :
    reformulatedProgramObjective logTail loss
        (originalToReformulated arrivalRate d) =
      originalProgramObjective loss d := by
  apply le_antisymm
  · exact original_binding_tightening_objective_le_of_pos
      hlogTail hmono hd.1
  · have href := originalToReformulated_feasible hlogTail hd.1
    have horiginal := reformulatedToOriginal_feasible
      hlogTail harrival href
    exact hd.2 _ horiginal

/-- A feasible-set/objective pair attains the value `v` at a minimizer. -/
def HasAttainedMinimum {Decision : Type*}
    (feasible : Decision → Prop) (objective : Decision → ℝ) (v : ℝ) : Prop :=
  ∃ d, AppliedModelingLib.Optimization.IsMinimizerOn feasible objective d ∧
    objective d = v

/-- Corrected Proposition 2.1 at the optimization level: the original joint
program and reciprocal program have exactly the same attained optimal values. -/
theorem correctedPrograms_same_attained_minimum
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {logTail totalCapacity v : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {loss : (Borough → Category → ℝ) → ℝ}
    (hlogTail : 0 < logTail)
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hmono : CoordinatewiseNondecreasing loss) :
    HasAttainedMinimum
        (OriginalProgramFeasible logTail totalCapacity arrivalRate)
        (originalProgramObjective loss) v ↔
      HasAttainedMinimum
        (ReformulatedProgramFeasible totalCapacity arrivalRate)
        (reformulatedProgramObjective logTail loss) v := by
  constructor
  · rintro ⟨d, hd, hvalue⟩
    refine ⟨originalToReformulated arrivalRate d,
      original_minimizer_maps_to_reformulated_minimizer
        hlogTail harrival hmono hd, ?_⟩
    rw [original_minimizer_binding_value_eq
      hlogTail harrival hmono hd, hvalue]
  · rintro ⟨d, hd, hvalue⟩
    refine ⟨reformulatedToOriginal logTail arrivalRate d,
      reformulated_minimizer_recovers_original_minimizer
        hlogTail harrival hmono hd, ?_⟩
    exact hvalue

/-- Source-hypothesis wrapper for corrected Proposition 2.1.  Convexity makes
the reciprocal formulation a convex program; value equivalence itself uses
only the weaker nondecreasing component. -/
theorem correctedPrograms_same_attained_minimum_of_convexNondecreasing
    {Borough Category : Type*}
    [Fintype Borough] [Fintype Category] [Nonempty Category]
    {logTail totalCapacity v : ℝ}
    {arrivalRate : Borough → Category → ℝ}
    {loss : (Borough → Category → ℝ) → ℝ}
    (hlogTail : 0 < logTail)
    (harrival : ∀ b k, 0 ≤ arrivalRate b k)
    (hloss : ConvexNondecreasingLoss loss) :
    HasAttainedMinimum
        (OriginalProgramFeasible logTail totalCapacity arrivalRate)
        (originalProgramObjective loss) v ↔
      HasAttainedMinimum
        (ReformulatedProgramFeasible totalCapacity arrivalRate)
        (reformulatedProgramObjective logTail loss) v :=
  correctedPrograms_same_attained_minimum
    hlogTail harrival hloss.nondecreasing

/-! ## Convexity of the corrected reciprocal objective -/

/-- Convex combination of two reciprocal-program decisions. -/
def reformulatedDecisionMix
    {Borough Category : Type*} (t : ℝ)
    (x y : ReformulatedProgramDecision Borough Category) :
    ReformulatedProgramDecision Borough Category where
  slack b k := t * x.slack b k + (1 - t) * y.slack b k
  boroughCapacity b :=
    t * x.boroughCapacity b + (1 - t) * y.boroughCapacity b

/-- The corrected reciprocal feasible set is convex. -/
theorem reformulatedProgramFeasible_mix
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    {totalCapacity t : ℝ} {arrivalRate : Borough → Category → ℝ}
    {x y : ReformulatedProgramDecision Borough Category}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : ReformulatedProgramFeasible totalCapacity arrivalRate x)
    (hy : ReformulatedProgramFeasible totalCapacity arrivalRate y) :
    ReformulatedProgramFeasible totalCapacity arrivalRate
      (reformulatedDecisionMix t x y) := by
  classical
  refine
    { slack_pos := ?_
      capacity_nonneg := ?_
      borough_slack := ?_
      budget := ?_ }
  · intro b k
    exact delayMix_pos ht0 ht1 (hx.slack_pos b) (hy.slack_pos b) k
  · intro b
    exact add_nonneg
      (mul_nonneg ht0 (hx.capacity_nonneg b))
      (mul_nonneg (sub_nonneg.mpr ht1) (hy.capacity_nonneg b))
  · intro b
    change
      ∑ k, (t * x.slack b k + (1 - t) * y.slack b k) ≤
        (t * x.boroughCapacity b + (1 - t) * y.boroughCapacity b) -
          ∑ k, arrivalRate b k
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.borough_slack b, hy.borough_slack b]
  · change
      ∑ b, (t * x.boroughCapacity b +
        (1 - t) * y.boroughCapacity b) ≤ totalCapacity
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.budget, hy.budget]

/-- For every convex coordinatewise nondecreasing loss, the corrected
reciprocal objective is convex along positive slack decisions. -/
theorem reformulatedProgramObjective_mix_le
    {Borough Category : Type*}
    {logTail t : ℝ} {loss : (Borough → Category → ℝ) → ℝ}
    {x y : ReformulatedProgramDecision Borough Category}
    (hlogTail : 0 ≤ logTail)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : ∀ b k, 0 < x.slack b k)
    (hy : ∀ b k, 0 < y.slack b k)
    (hmono : CoordinatewiseNondecreasing loss)
    (hconvex : CoordinatewiseConvex loss) :
    reformulatedProgramObjective logTail loss
        (reformulatedDecisionMix t x y) ≤
      t * reformulatedProgramObjective logTail loss x +
        (1 - t) * reformulatedProgramObjective logTail loss y := by
  calc
    reformulatedProgramObjective logTail loss
        (reformulatedDecisionMix t x y) ≤
        loss (fun b k ↦
          t * bindingSLADelay logTail (x.slack b k) +
            (1 - t) * bindingSLADelay logTail (y.slack b k)) := by
      apply hmono
      intro b k
      exact weighted_reciprocal_mix_le hlogTail ht0 ht1
        (hx b k) (hy b k)
    _ ≤ t * reformulatedProgramObjective logTail loss x +
        (1 - t) * reformulatedProgramObjective logTail loss y := by
      exact hconvex ht0 ht1 _ _

/-! ## Arbitrary finite-Borough strict centralization -/

/-- Square root is subadditive on nonnegative reals. -/
theorem sqrt_add_le_add_sqrt_of_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hleft : 0 ≤ Real.sqrt (a + b) := Real.sqrt_nonneg _
  have hright : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have ha_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hb_sq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have hab_sq : (Real.sqrt (a + b)) ^ 2 = a + b :=
    Real.sq_sqrt hab
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Finite square-root subadditivity. -/
theorem sqrt_sum_le_sum_sqrt
    {I : Type*} (s : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (sqrt_add_le_add_sqrt_of_nonneg
        (hf a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))).trans
        (add_le_add (le_refl _)
          (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))))

/-- With at least two positive finite summands, square-root subadditivity is
strict.  This is the missing cardinality hypothesis in current Proposition 2.6. -/
theorem sqrt_sum_lt_sum_sqrt_of_nontrivial
    {I : Type*} [Fintype I] [Nontrivial I]
    (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    Real.sqrt (∑ i, f i) < ∑ i, Real.sqrt (f i) := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  have hjmem : j ∈ (Finset.univ.erase i) := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hrest : 0 < ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_pos (fun j _hj ↦ hf j) ⟨j, hjmem⟩
  have hsplit :
      (∑ j ∈ Finset.univ.erase i, f j) + f i = ∑ j, f j :=
    Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hsplitsqrt :
      (∑ j ∈ Finset.univ.erase i, Real.sqrt (f j)) + Real.sqrt (f i) =
        ∑ j, Real.sqrt (f j) :=
    Finset.sum_erase_add Finset.univ (fun j ↦ Real.sqrt (f j))
      (Finset.mem_univ i)
  have hstrict := sqrt_add_lt_add_sqrt_of_pos hrest (hf i)
  have hweak := sqrt_sum_le_sum_sqrt (Finset.univ.erase i) f
    (fun j _hj ↦ (hf j).le)
  rw [← hsplit, ← hsplitsqrt]
  exact hstrict.trans_le (add_le_add hweak (le_refl _))

/-- Pooled city square-root normalizer. -/
def finiteCityRootNormalizer
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    (weight : Borough → Category → ℝ) : ℝ :=
  ∑ k, Real.sqrt (∑ b, weight b k)

/-- Borough-specific square-root normalizer before pooling. -/
def finiteDecentralizedRootNormalizer
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    (weight : Borough → Category → ℝ) : ℝ :=
  ∑ k, ∑ b, Real.sqrt (weight b k)

/-- Extreme-efficiency city delay for a pooled category. -/
def finiteCityEfficiencyDelay
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    (logTail excessCapacity : ℝ)
    (weight : Borough → Category → ℝ) (k : Category) : ℝ :=
  logTail / excessCapacity * finiteCityRootNormalizer weight /
    Real.sqrt (∑ b, weight b k)

/-- Extreme-efficiency Borough-category delay before pooling. -/
def finiteDecentralizedEfficiencyDelay
    {Borough Category : Type*} [Fintype Borough] [Fintype Category]
    (logTail excessCapacity : ℝ)
    (weight : Borough → Category → ℝ) (b : Borough) (k : Category) : ℝ :=
  logTail / excessCapacity * finiteDecentralizedRootNormalizer weight /
    Real.sqrt (weight b k)

/-- Pooling strictly lowers the aggregate square-root numerator whenever every
category has at least two positive Borough loads. -/
theorem finiteCityRootNormalizer_lt_decentralized
    {Borough Category : Type*}
    [Fintype Borough] [Nontrivial Borough]
    [Fintype Category] [Nonempty Category]
    {weight : Borough → Category → ℝ}
    (hweight : ∀ b k, 0 < weight b k) :
    finiteCityRootNormalizer weight <
      finiteDecentralizedRootNormalizer weight := by
  classical
  unfold finiteCityRootNormalizer finiteDecentralizedRootNormalizer
  apply Finset.sum_lt_sum
  · intro k _hk
    exact (sqrt_sum_lt_sum_sqrt_of_nontrivial
      (fun b ↦ weight b k) (fun b ↦ hweight b k)).le
  · obtain ⟨k⟩ := ‹Nonempty Category›
    exact ⟨k, Finset.mem_univ k,
      sqrt_sum_lt_sum_sqrt_of_nontrivial
        (fun b ↦ weight b k) (fun b ↦ hweight b k)⟩

/-- General corrected Proposition 2.6: with a nontrivial finite Borough set,
positive cell loads, positive log-tail, and positive excess capacity, the
pooled city SLA is strictly shorter in every Borough-category cell. -/
theorem finiteCityEfficiencyDelay_lt_decentralized
    {Borough Category : Type*}
    [Fintype Borough] [Nontrivial Borough]
    [Fintype Category] [Nonempty Category]
    {logTail excessCapacity : ℝ}
    {weight : Borough → Category → ℝ}
    (hlogTail : 0 < logTail) (hexcess : 0 < excessCapacity)
    (hweight : ∀ b k, 0 < weight b k) (b : Borough) (k : Category) :
    finiteCityEfficiencyDelay logTail excessCapacity weight k <
      finiteDecentralizedEfficiencyDelay logTail excessCapacity weight b k := by
  apply abstractCentralizedEndpoint_strictly_better
    hlogTail hexcess
  · exact Finset.sum_nonneg (fun k _hk ↦ Real.sqrt_nonneg _)
  · exact finiteCityRootNormalizer_lt_decentralized hweight
  · exact Real.sqrt_pos.2 (hweight b k)
  · apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum
      (fun b _hb ↦ (hweight b k).le) (Finset.mem_univ b)

end

end LG24ServiceLevelAgreements

import AppliedModelingLib.Foundations.Optimization.Certificate
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Pointwise Suprema

Reusable order-theoretic facts for a pointwise supremum of real-valued
payoffs. Unlike a finite argmax, this layer needs no selected maximizer: all
claims expose the boundedness needed by `sSup`. It is useful for robust
optimization on a non-finite action space, where measurable selection and
attainment are separate assumptions rather than hidden in the definition.
-/

namespace AppliedModelingLib
namespace Optimization

variable {Action State : Type*}

/-- The pointwise supremum of a payoff family over its action argument. -/
noncomputable def pointwiseSupremum (payoff : Action → State → ℝ) (state : State) : ℝ :=
  sSup (Set.range fun action => payoff action state)

/-- An attainable payoff lies below its bounded pointwise supremum. -/
theorem payoff_le_pointwiseSupremum (payoff : Action → State → ℝ)
    (action : Action) (state : State)
    (hbounded : BddAbove (Set.range fun candidate => payoff candidate state)) :
    payoff action state ≤ pointwiseSupremum payoff state := by
  exact le_csSup hbounded (Set.mem_range_self action)

/-- A pointwise upper bound also bounds the pointwise supremum. -/
theorem pointwiseSupremum_le_of_forall_le [Nonempty Action]
    (payoff : Action → State → ℝ) (state : State) (bound : ℝ)
    (hupper : ∀ action, payoff action state ≤ bound) :
    pointwiseSupremum payoff state ≤ bound := by
  unfold pointwiseSupremum
  refine csSup_le (Set.range_nonempty _) ?_
  rintro value ⟨action, rfl⟩
  exact hupper action

/--
A countable family of measurable action-valued candidates yields a measurable
near-maximizing selector whenever one candidate is pointwise within `epsilon`
of a measurable envelope.  The candidates may depend measurably on the state.

This theorem directly uses Mathlib's
[`measurable_find`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html#measurable_find)
and
[`measurable_from_prod_countable_right`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html#measurable_from_prod_countable_right)
from
[`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean),
at the repository-pinned Apache-2.0 revision.  Those upstream APIs are used
unchanged; the local theorem only composes their countable-index and
action-valued measurability conclusions, and copies no upstream proof text.
-/
theorem exists_measurable_selector_of_countable_near_maximizers
    [MeasurableSpace Action] [MeasurableSpace State]
    (payoff : Action → State → ℝ) (envelope : State → ℝ)
    (candidates : ℕ → State → Action) (epsilon : ℝ)
    (henvelope : Measurable envelope)
    (hcandidate : ∀ n, Measurable (candidates n))
    (hpayoff : ∀ n, Measurable fun state => payoff (candidates n state) state)
    (hnear : ∀ state, ∃ n, envelope state ≤ payoff (candidates n state) state + epsilon) :
    ∃ selector : State → Action, Measurable selector ∧
      ∀ state, envelope state ≤ payoff (selector state) state + epsilon := by
  classical
  let predicate : State → ℕ → Prop := fun state n =>
    envelope state ≤ payoff (candidates n state) state + epsilon
  have hpredicate_measurable : ∀ n, MeasurableSet {state | predicate state n} := by
    intro n
    exact measurableSet_le henvelope ((hpayoff n).add measurable_const)
  have hindex_measurable : Measurable (fun state => Nat.find (hnear state)) := by
    exact measurable_find hnear hpredicate_measurable
  refine ⟨fun state => candidates (Nat.find (hnear state)) state, ?_, ?_⟩
  · have huncurried : Measurable (fun pair : ℕ × State => candidates pair.1 pair.2) :=
      measurable_from_prod_countable_right hcandidate
    exact huncurried.comp (hindex_measurable.prodMk measurable_id)
  · intro state
    exact Nat.find_spec (hnear state)

/--
On a separable metric action space, continuity in the action variable reduces
measurable near-maximizer selection to the countable dense sequence.  The
state-variable measurability of every fixed action remains explicit.

This specializes the preceding countable-candidate selector to the
continuous/separable route used by Euclidean robust-optimization models; it
does not attempt to formalize selection for arbitrary normal integrands.
Mathlib supplies
[`denseSeq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html#denseSeq),
[`DenseRange.exists_mem_open`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Continuous.html#DenseRange.exists_mem_open),
and
[`exists_lt_of_lt_csSup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/ConditionallyCompleteLattice/Basic.html#exists_lt_of_lt_csSup)
from the repository-pinned Apache-2.0 Mathlib revision.  Those APIs are used
unchanged; the dense-sequence near-maximizer argument is local and copies no
upstream proof text.
-/
theorem exists_measurable_selector_of_separable_continuous_near_maximizers
    [MeasurableSpace Action] [PseudoMetricSpace Action] [BorelSpace Action]
    [TopologicalSpace.SeparableSpace Action] [Nonempty Action] [MeasurableSpace State]
    (payoff : Action → State → ℝ) (epsilon : ℝ)
    (henvelope : Measurable (pointwiseSupremum payoff))
    (hpayoff_action_continuous : ∀ state, Continuous fun action => payoff action state)
    (hpayoff_state_measurable : ∀ action, Measurable fun state => payoff action state)
    (hbounded : ∀ state, BddAbove (Set.range fun action => payoff action state))
    (hepsilon : 0 < epsilon) :
    ∃ selector : State → Action, Measurable selector ∧
      ∀ state, pointwiseSupremum payoff state ≤
        payoff (selector state) state + epsilon := by
  let candidates : ℕ → State → Action := fun n _ => TopologicalSpace.denseSeq Action n
  have hnear : ∀ state, ∃ n,
      pointwiseSupremum payoff state ≤ payoff (candidates n state) state + epsilon := by
    intro state
    unfold pointwiseSupremum
    have hlt : sSup (Set.range fun action => payoff action state) - epsilon / 2 <
        sSup (Set.range fun action => payoff action state) := by
      linarith
    obtain ⟨_, ⟨action, rfl⟩, haction⟩ :=
      (lt_csSup_iff (hbounded state)
        (Set.range_nonempty fun action => payoff action state)).mp hlt
    have hopen : IsOpen ((fun action => payoff action state) ⁻¹'
        Set.Ioi (payoff action state - epsilon / 2)) :=
      isOpen_Ioi.preimage (hpayoff_action_continuous state)
    have hopen_nonempty : ((fun action => payoff action state) ⁻¹'
        Set.Ioi (payoff action state - epsilon / 2)).Nonempty := by
      refine ⟨action, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi]
      linarith
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq Action).exists_mem_open
      hopen hopen_nonempty
    change TopologicalSpace.denseSeq Action n ∈ (fun action => payoff action state) ⁻¹'
      Set.Ioi (payoff action state - epsilon / 2) at hn
    simp only [Set.mem_preimage, Set.mem_Ioi] at hn
    have hresult : sSup (Set.range fun action => payoff action state) ≤
        payoff (TopologicalSpace.denseSeq Action n) state + epsilon := by
      linarith
    exact ⟨n, by simpa [candidates] using hresult⟩
  exact exists_measurable_selector_of_countable_near_maximizers payoff
    (pointwiseSupremum payoff) candidates epsilon henvelope
    (fun _ => measurable_const) (fun n => by
      simpa [candidates] using hpayoff_state_measurable (TopologicalSpace.denseSeq Action n)) hnear

/--
Uniform perturbations of a bounded payoff family perturb its pointwise
supremum by at most the same amount. No supremum attainment is assumed.
-/
theorem abs_pointwiseSupremum_sub_le_of_forall_abs_sub_le [Nonempty Action]
    (first second : Action → State → ℝ) (bound : ℝ)
    (hfirst_bounded : ∀ state, BddAbove (Set.range fun action => first action state))
    (hsecond_bounded : ∀ state, BddAbove (Set.range fun action => second action state))
    (hbound : ∀ action state, |first action state - second action state| ≤ bound)
    (state : State) :
    |pointwiseSupremum first state - pointwiseSupremum second state| ≤ bound := by
  apply abs_le.mpr
  constructor
  · have hupper : pointwiseSupremum second state ≤ pointwiseSupremum first state + bound := by
      apply pointwiseSupremum_le_of_forall_le
      intro action
      calc
        second action state ≤ first action state + bound := by
          linarith [(abs_le.mp (hbound action state)).1]
        _ ≤ pointwiseSupremum first state + bound :=
          add_le_add (payoff_le_pointwiseSupremum first action state
            (hfirst_bounded state)) (le_refl bound)
    linarith
  · have hupper : pointwiseSupremum first state ≤ pointwiseSupremum second state + bound := by
      apply pointwiseSupremum_le_of_forall_le
      intro action
      calc
        first action state ≤ second action state + bound := by
          linarith [(abs_le.mp (hbound action state)).2]
        _ ≤ pointwiseSupremum second state + bound :=
          add_le_add (payoff_le_pointwiseSupremum second action state
            (hsecond_bounded state)) (le_refl bound)
    linarith

/-- The pointwise payoff for one penalized robust-optimization objective. -/
def penalizedPayoff (loss : Action → ℝ) (cost : Action → State → ℝ)
    (penalty : ℝ) : Action → State → ℝ :=
  fun action state => loss action - penalty * cost action state

/-- At zero penalty, the penalized pointwise envelope is the state-independent
supremum of the loss. -/
theorem pointwiseSupremum_penalizedPayoff_zero (loss : Action → ℝ)
    (cost : Action → State → ℝ) (state : State) :
    pointwiseSupremum (penalizedPayoff loss cost 0) state = sSup (Set.range loss) := by
  unfold pointwiseSupremum penalizedPayoff
  congr with action
  simp

/--
For every fixed state, a finite pointwise supremum of affine penalized
payoffs is convex in the penalty.  The boundedness premise makes each real
supremum semantically meaningful.

This directly uses Mathlib's `ConvexOn` API from
[`Mathlib/Analysis/Convex/Function.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/Function.lean)
at the repository-pinned Apache-2.0 revision.  The affine-envelope proof is
local and copies no upstream proof text.
-/
theorem convexOn_pointwiseSupremum_penalizedPayoff [Nonempty Action]
    (penaltySet : Set ℝ) (hpenaltySet : Convex ℝ penaltySet)
    (loss : Action → ℝ) (cost : Action → State → ℝ)
    (hbounded : ∀ penalty ∈ penaltySet, ∀ state,
      BddAbove (Set.range fun action => penalizedPayoff loss cost penalty action state))
    (state : State) :
    ConvexOn ℝ penaltySet (fun penalty =>
      pointwiseSupremum (penalizedPayoff loss cost penalty) state) := by
  refine ⟨hpenaltySet, ?_⟩
  intro first hfirstMem second hsecondMem firstWeight secondWeight hfirstWeight hsecondWeight hweights
  apply pointwiseSupremum_le_of_forall_le
  intro action
  have hfirst := payoff_le_pointwiseSupremum
    (penalizedPayoff loss cost first) action state (hbounded first hfirstMem state)
  have hsecond := payoff_le_pointwiseSupremum
    (penalizedPayoff loss cost second) action state (hbounded second hsecondMem state)
  have hfirst' : loss action - first * cost action state ≤
      pointwiseSupremum (penalizedPayoff loss cost first) state := by
    simpa [penalizedPayoff] using hfirst
  have hsecond' : loss action - second * cost action state ≤
      pointwiseSupremum (penalizedPayoff loss cost second) state := by
    simpa [penalizedPayoff] using hsecond
  unfold penalizedPayoff
  rw [smul_eq_mul, smul_eq_mul]
  calc
    loss action - (firstWeight * first + secondWeight * second) * cost action state =
        (firstWeight + secondWeight) * loss action -
          firstWeight * first * cost action state - secondWeight * second * cost action state := by
      rw [hweights]
      ring
    _ = firstWeight * (loss action - first * cost action state) +
          secondWeight * (loss action - second * cost action state) := by ring
    _ ≤ firstWeight * pointwiseSupremum (penalizedPayoff loss cost first) state +
          secondWeight * pointwiseSupremum (penalizedPayoff loss cost second) state := by
      gcongr
    _ = firstWeight • pointwiseSupremum (penalizedPayoff loss cost first) state +
          secondWeight • pointwiseSupremum (penalizedPayoff loss cost second) state := by
      simp only [smul_eq_mul]

/--
On a positive penalty range, bounded loss and a zero-cost reference action
give an explicit modulus for the loss of the pointwise penalized envelope as
the penalty increases.  The bound is relative to the smaller penalty, which
is necessary when costs are not uniformly bounded.

No maximizer is selected: actions with cost above `2 * scale / firstPenalty`
are already no better than the reference payoff, while the remaining actions
are compared directly.  This is the deterministic ingredient for finite
geometric penalty brackets on compact intervals bounded away from zero.
-/
theorem pointwiseSupremum_penalizedPayoff_sub_le_relative_penalty
    [Nonempty Action] (loss : Action → ℝ) (cost : Action → State → ℝ)
    (reference : State → Action) (scale : ℝ) (hscale : 0 ≤ scale)
    (hloss_abs_le : ∀ action, |loss action| ≤ scale)
    (hcost_nonneg : ∀ action state, 0 ≤ cost action state)
    (hreference_cost_zero : ∀ state, cost (reference state) state = 0)
    (firstPenalty secondPenalty : ℝ) (hfirstPenalty : 0 < firstPenalty)
    (hpenalty : firstPenalty ≤ secondPenalty) (state : State) :
    pointwiseSupremum (penalizedPayoff loss cost firstPenalty) state -
        pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state ≤
      2 * scale * ((secondPenalty - firstPenalty) / firstPenalty) := by
  have hsecondPenalty : 0 ≤ secondPenalty := (le_of_lt hfirstPenalty).trans hpenalty
  have hbounded : ∀ penalty, 0 ≤ penalty → ∀ state,
      BddAbove (Set.range fun action => penalizedPayoff loss cost penalty action state) := by
    intro penalty hpenalty_nonneg state
    refine bddAbove_range_of_forall_le _ (M := scale) ?_
    intro action
    unfold penalizedPayoff
    exact (sub_le_self _ (mul_nonneg hpenalty_nonneg (hcost_nonneg action state))).trans
      (abs_le.mp (hloss_abs_le action)).2
  have href : -scale ≤ pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state := by
    calc
      -scale ≤ loss (reference state) := (abs_le.mp (hloss_abs_le (reference state))).1
      _ = penalizedPayoff loss cost secondPenalty (reference state) state := by
        simp only [penalizedPayoff, hreference_cost_zero, mul_zero, sub_zero]
      _ ≤ pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state :=
        payoff_le_pointwiseSupremum _ _ _ (hbounded secondPenalty hsecondPenalty state)
  apply (sub_le_iff_le_add).2
  apply pointwiseSupremum_le_of_forall_le
  intro action
  have hsecond := payoff_le_pointwiseSupremum
    (penalizedPayoff loss cost secondPenalty) action state
      (hbounded secondPenalty hsecondPenalty state)
  have hsecond' : loss action - secondPenalty * cost action state ≤
      pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state := by
    simpa [penalizedPayoff] using hsecond
  by_cases hcost : cost action state ≤ 2 * scale / firstPenalty
  · have hpenalty_gap : 0 ≤ secondPenalty - firstPenalty := sub_nonneg.mpr hpenalty
    have hcost_gap : (secondPenalty - firstPenalty) * cost action state ≤
        (secondPenalty - firstPenalty) * (2 * scale / firstPenalty) :=
      mul_le_mul_of_nonneg_left hcost hpenalty_gap
    calc
      penalizedPayoff loss cost firstPenalty action state =
          (loss action - secondPenalty * cost action state) +
            (secondPenalty - firstPenalty) * cost action state := by
        unfold penalizedPayoff
        ring
      _ ≤ pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state +
          (secondPenalty - firstPenalty) * cost action state := by
        gcongr
      _ ≤ pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state +
          (secondPenalty - firstPenalty) * (2 * scale / firstPenalty) := by
        gcongr
      _ = 2 * scale * ((secondPenalty - firstPenalty) / firstPenalty) +
          pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state := by
        field_simp [ne_of_gt hfirstPenalty] ; ring_nf
  · have hcost_gt : 2 * scale / firstPenalty < cost action state := lt_of_not_ge hcost
    have hmult : 2 * scale < firstPenalty * cost action state := by
      simpa [mul_comm] using (div_lt_iff₀ hfirstPenalty).mp hcost_gt
    have hrelative : penalizedPayoff loss cost firstPenalty action state ≤
        pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state := by
      apply le_of_lt
      calc
          penalizedPayoff loss cost firstPenalty action state =
              loss action - firstPenalty * cost action state := rfl
          _ ≤ scale - firstPenalty * cost action state := by
            gcongr
            exact (abs_le.mp (hloss_abs_le action)).2
          _ < scale - 2 * scale := by linarith
          _ = -scale := by ring
          _ ≤ pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state := href
    have hrelative_nonneg : 0 ≤ 2 * scale * ((secondPenalty - firstPenalty) / firstPenalty) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hscale)
        (div_nonneg (sub_nonneg.mpr hpenalty) (le_of_lt hfirstPenalty))
    exact hrelative.trans (le_add_of_nonneg_left hrelative_nonneg)

/--
For a nonnegative pointwise cost, increasing a penalty can only decrease the
pointwise supremum of penalized payoffs.  The bounded-above premise is stated
on the smaller-penalty payoff, which is exactly what the `sSup` comparison
uses; no maximizer is selected.
-/
theorem pointwiseSupremum_penalizedPayoff_antitone_of_nonneg_cost [Nonempty Action]
    (loss : Action → ℝ) (cost : Action → State → ℝ) (firstPenalty secondPenalty : ℝ)
    (hfirst_bounded : ∀ state,
      BddAbove (Set.range fun action =>
        penalizedPayoff loss cost firstPenalty action state))
    (hcost_nonneg : ∀ action state, 0 ≤ cost action state)
    (hpenalty : firstPenalty ≤ secondPenalty) (state : State) :
    pointwiseSupremum (penalizedPayoff loss cost secondPenalty) state ≤
      pointwiseSupremum (penalizedPayoff loss cost firstPenalty) state := by
  apply pointwiseSupremum_le_of_forall_le
  intro action
  calc
    penalizedPayoff loss cost secondPenalty action state ≤
        penalizedPayoff loss cost firstPenalty action state := by
      unfold penalizedPayoff
      linarith [mul_le_mul_of_nonneg_right hpenalty (hcost_nonneg action state)]
    _ ≤ pointwiseSupremum (penalizedPayoff loss cost firstPenalty) state :=
      payoff_le_pointwiseSupremum _ action state (hfirst_bounded state)

/--
A bounded loss gives the same absolute bound for its non-finite penalized
pointwise supremum when the cost is nonnegative, its diagonal is zero, and the
penalty is nonnegative. The lower bound uses the diagonal action and the
upper bound uses `csSup_le`; no argmax is needed.
-/
theorem abs_pointwiseSupremum_penalizedPayoff_le_of_loss_abs_le_selfCost_zero
    {State : Type*} [Nonempty State]
    (loss : State → ℝ) (cost : State → State → ℝ) (penalty bound : ℝ)
    (hloss : ∀ state, |loss state| ≤ bound)
    (hcost : ∀ first second, 0 ≤ cost first second)
    (hselfCost : ∀ state, cost state state = 0)
    (hpenalty : 0 ≤ penalty) (state : State) :
    |pointwiseSupremum (penalizedPayoff loss cost penalty) state| ≤ bound := by
  apply abs_le.mpr
  constructor
  · have hbounded : BddAbove (Set.range fun action =>
        penalizedPayoff loss cost penalty action state) :=
      bddAbove_range_of_forall_le _ (fun action => by
        unfold penalizedPayoff
        exact (sub_le_self _ (mul_nonneg hpenalty (hcost action state))).trans
          (abs_le.mp (hloss action)).2)
    calc
      -bound ≤ loss state := (abs_le.mp (hloss state)).1
      _ = penalizedPayoff loss cost penalty state state := by
        unfold penalizedPayoff
        rw [hselfCost state]
        ring
      _ ≤ pointwiseSupremum (penalizedPayoff loss cost penalty) state :=
        payoff_le_pointwiseSupremum _ state state hbounded
  · apply pointwiseSupremum_le_of_forall_le
    intro action
    unfold penalizedPayoff
    exact (sub_le_self _ (mul_nonneg hpenalty (hcost action state))).trans
      (abs_le.mp (hloss action)).2

/--
Parameterwise loss perturbations pass unchanged through a penalized pointwise
supremum once each payoff range is bounded above.
-/
theorem abs_pointwiseSupremum_penalizedPayoff_sub_le_of_forall_abs_sub_le [Nonempty Action]
    (first second : Action → ℝ) (cost : Action → State → ℝ) (penalty bound : ℝ)
    (hfirst_bounded : ∀ state,
      BddAbove (Set.range fun action => penalizedPayoff first cost penalty action state))
    (hsecond_bounded : ∀ state,
      BddAbove (Set.range fun action => penalizedPayoff second cost penalty action state))
    (hbound : ∀ action, |first action - second action| ≤ bound) (state : State) :
    |pointwiseSupremum (penalizedPayoff first cost penalty) state -
      pointwiseSupremum (penalizedPayoff second cost penalty) state| ≤ bound := by
  apply abs_pointwiseSupremum_sub_le_of_forall_abs_sub_le
    (hfirst_bounded := hfirst_bounded) (hsecond_bounded := hsecond_bounded)
  intro action nominal
  have hrewrite :
      penalizedPayoff first cost penalty action nominal -
          penalizedPayoff second cost penalty action nominal = first action - second action := by
    simp only [penalizedPayoff]
    ring
  rw [hrewrite]
  exact hbound action

end Optimization
end AppliedModelingLib

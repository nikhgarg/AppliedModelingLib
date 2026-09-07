import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.UnitInterval
import AppliedModelingLib.Foundations.Math.FixedPoint.KKM

open scoped unitInterval
open unitInterval

/-!
# Security notions for discontinuous games

This file provides the local topological predicates used in equilibrium
existence theorems for discontinuous games.  The definitions deliberately
separate an action chosen to secure a payoff from the deviation whose payoff
sets the target level.  That distinction is required by the corrected
diagonal-payoff-security definition in Ewerhart--Reny (2022).

The file does **not** state an equilibrium-existence theorem.  Such a theorem
requires additional compactness, convexity, quasiconcavity, and (for the
symmetric mixed result) mixed-extension quasisymmetry hypotheses.
-/

namespace AppliedModelingLib

/--
`action` secures payoff `value` at state `x` when its payoff stays strictly
above `value` throughout one neighborhood of `x`.
-/
def SecuresPayoffAt {Action State : Type*} [TopologicalSpace State]
    (payoff : Action → State → ℝ) (action : Action) (value : ℝ) (x : State) : Prop :=
  ∃ U : Set State, U ∈ nhds x ∧ ∀ x' : State, x' ∈ U → value < payoff action x'

/-- A secured payoff may be weakened without changing the securing action. -/
theorem SecuresPayoffAt.mono {Action State : Type*} [TopologicalSpace State]
    {payoff : Action → State → ℝ} {action : Action} {value value' : ℝ} {x : State}
    (hsecure : SecuresPayoffAt payoff action value x) (hvalue : value' ≤ value) :
    SecuresPayoffAt payoff action value' x := by
  rcases hsecure with ⟨U, hU, hpayoff⟩
  refine ⟨U, hU, ?_⟩
  intro x' hx'
  exact lt_of_le_of_lt hvalue (hpayoff x' hx')

/--
Security is preserved when the opponent-state space is pulled back along a
continuous map.  This is used when compact-subtype mixed strategies are
embedded into ambient mixed strategies by push-forward.
-/
theorem SecuresPayoffAt.comp_continuous
    {Action State State' : Type*} [TopologicalSpace State] [TopologicalSpace State']
    {payoff : Action → State → ℝ} {stateMap : State' → State}
    {action : Action} {value : ℝ} {state : State'}
    (hsecure : SecuresPayoffAt payoff action value (stateMap state))
    (hcontinuous : Continuous stateMap) :
    SecuresPayoffAt (fun action state' => payoff action (stateMap state')) action value state := by
  rcases hsecure with ⟨U, hU, hpayoff⟩
  refine ⟨stateMap ⁻¹' U, ?_, ?_⟩
  · exact hcontinuous.continuousAt.preimage_mem_nhds hU
  · intro state' hstate'
    exact hpayoff (stateMap state') hstate'

/--
Corrected diagonal payoff security for a symmetric one-action payoff model.
For every diagonal state `x`, deviation `y`, and positive tolerance, some
action must secure the payoff of **that deviation** at `x`, less the tolerance.
The target's dependence on `y` is the correction recorded by
Ewerhart--Reny (2022) to Reny (1999).
-/
def DiagonallyPayoffSecure {Action : Type*} [TopologicalSpace Action]
    (payoff : Action → Action → ℝ) : Prop :=
  ∀ x y : Action, ∀ ε : ℝ, 0 < ε →
    ∃ securingAction : Action,
      SecuresPayoffAt payoff securingAction (payoff y x - ε) x

/--
Corrected diagonal payoff security when deviations are pure actions and the
diagonal state is a (possibly mixed) state space.  This is the precise
intermediate notion needed to lift a pure-action construction to a mixed game;
it should not be confused with diagonal payoff security of the mixed extension
itself.
-/
def PureDiagonalPayoffSecureOn {PureAction State : Type*} [TopologicalSpace State]
    (actionSet : Set PureAction) (payoff : PureAction → State → ℝ) : Prop :=
  ∀ x : State, ∀ y : PureAction, y ∈ actionSet → ∀ ε : ℝ, 0 < ε →
    ∃ securingAction : PureAction, securingAction ∈ actionSet ∧
      SecuresPayoffAt payoff securingAction (payoff y x - ε) x

/--
Plan's mixed-quasi-symmetry condition for a game with a common pure-action
space and common mixed-action space.  A player who uses pure action `x` while
every opponent uses the same mixed action `μ` receives the same payoff for
every player label.  This is equivalent to quasisymmetry of the mixed
extension in the setting used by the corrected Reny Corollary 5.3.
-/
def MixedQuasiSymmetric {Player PureAction MixedAction : Type*}
    (payoff : Player → PureAction → MixedAction → ℝ) : Prop :=
  ∀ i j : Player, ∀ x : PureAction, ∀ μ : MixedAction,
    payoff i x μ = payoff j x μ

/--
The payoff of a mixed action in the mixed extension of a pure-action payoff
model.  The opponent state is kept explicit because a discontinuous game need
not be jointly continuous in its action and opponent-profile arguments.
-/
noncomputable def MixedExtensionPayoff {PureAction State : Type*}
    [MeasurableSpace PureAction] (payoff : PureAction → State → ℝ)
    (strategy : MeasureTheory.ProbabilityMeasure PureAction) (state : State) : ℝ :=
  ∫ action, payoff action state ∂strategy.toMeasure

/--
The binary convex mixture of probability measures.  We keep it as an explicit
operation rather than imposing a vector-space structure on probability laws;
the latter are an affine, not linear, space.
-/
noncomputable def probabilityMeasureMix {Action : Type*} [MeasurableSpace Action]
    (weight : I) (left right : MeasureTheory.ProbabilityMeasure Action) :
    MeasureTheory.ProbabilityMeasure Action :=
  ⟨unitInterval.toNNReal weight • left.toMeasure +
      unitInterval.toNNReal (σ weight) • right.toMeasure,
    inferInstance⟩

@[simp]
theorem probabilityMeasureMix_toMeasure {Action : Type*} [MeasurableSpace Action]
    (weight : I) (left right : MeasureTheory.ProbabilityMeasure Action) :
    (probabilityMeasureMix weight left right).toMeasure =
      unitInterval.toNNReal weight • left.toMeasure +
        unitInterval.toNNReal (σ weight) • right.toMeasure := rfl

/-- The finite-measure coercion of a probability-law mixture is the affine mixture. -/
@[simp]
theorem probabilityMeasureMix_toFiniteMeasure {Action : Type*} [MeasurableSpace Action]
    (weight : I) (left right : MeasureTheory.ProbabilityMeasure Action) :
    (probabilityMeasureMix weight left right).toFiniteMeasure =
      unitInterval.toNNReal weight • left.toFiniteMeasure +
        unitInterval.toNNReal (σ weight) • right.toFiniteMeasure := by
  apply MeasureTheory.FiniteMeasure.toMeasure_injective
  rfl

/--
Probability-law mixing is continuous for the weak topology.  Together with
compactness of laws on a compact action space, this supplies the genuine
topological-convexity input needed by a later fixed-point theorem; it is not
merely an algebraic mixture identity.
-/
theorem continuous_probabilityMeasureMix {Action : Type*}
    [MeasurableSpace Action] [TopologicalSpace Action] [OpensMeasurableSpace Action] :
    Continuous (fun strategies : I ×
      (MeasureTheory.ProbabilityMeasure Action × MeasureTheory.ProbabilityMeasure Action) =>
        probabilityMeasureMix strategies.1 strategies.2.1 strategies.2.2) := by
  refine (MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding Action).continuous_iff.mpr ?_
  change Continuous (fun strategies : I ×
      (MeasureTheory.ProbabilityMeasure Action × MeasureTheory.ProbabilityMeasure Action) =>
        (probabilityMeasureMix strategies.1 strategies.2.1 strategies.2.2).toFiniteMeasure)
  simp_rw [probabilityMeasureMix_toFiniteMeasure]
  exact
    ((unitInterval.toNNReal_continuous.comp continuous_fst).smul
      (MeasureTheory.ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd.fst)).add
    ((unitInterval.toNNReal_continuous.comp (continuous_symm.comp continuous_fst)).smul
      (MeasureTheory.ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd.snd))

/-- The nonnegative coefficient represented by one coordinate of a real standard simplex. -/
def simplexWeightNNReal {Index : Type*} [Fintype Index]
    (weights : stdSimplex ℝ Index) (i : Index) : NNReal :=
  ⟨weights i, stdSimplex.zero_le weights i⟩

@[simp]
theorem coe_simplexWeightNNReal {Index : Type*} [Fintype Index]
    (weights : stdSimplex ℝ Index) (i : Index) :
    (simplexWeightNNReal weights i : ℝ) = weights i := rfl

/-- The finite barycenter of probability measures with standard-simplex weights. -/
noncomputable def finiteProbabilityMeasureBarycenter
    {Action Index : Type*} [MeasurableSpace Action] [Fintype Index]
    (weights : stdSimplex ℝ Index) (strategies : Index → MeasureTheory.ProbabilityMeasure Action) :
    MeasureTheory.ProbabilityMeasure Action :=
  ⟨∑ i, simplexWeightNNReal weights i • (strategies i).toMeasure, by
    classical
    rw [MeasureTheory.isProbabilityMeasure_iff]
    let measures : Index → MeasureTheory.Measure Action :=
      fun i => simplexWeightNNReal weights i • (strategies i).toMeasure
    have hsum_apply : ∀ s : Finset Index,
        (∑ i ∈ s, measures i) Set.univ = ∑ i ∈ s, measures i Set.univ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => simp [hi, MeasureTheory.Measure.add_apply, ih]
    change (∑ i, measures i) Set.univ = 1
    rw [hsum_apply]
    dsimp [measures]
    simp only [MeasureTheory.measure_univ, mul_one]
    change ∑ i, (simplexWeightNNReal weights i : ENNReal) = 1
    have hweights : ∑ i, simplexWeightNNReal weights i = 1 := by
      apply NNReal.eq
      simp only [NNReal.coe_sum]
      calc
        ∑ i, (simplexWeightNNReal weights i : ℝ) = ∑ i, weights i :=
          Finset.sum_congr rfl fun i _ => coe_simplexWeightNNReal weights i
        _ = 1 := stdSimplex.sum_eq_one weights
    exact_mod_cast hweights⟩

@[simp]
theorem finiteProbabilityMeasureBarycenter_toFiniteMeasure
    {Action Index : Type*} [MeasurableSpace Action] [Fintype Index]
    (weights : stdSimplex ℝ Index) (strategies : Index → MeasureTheory.ProbabilityMeasure Action) :
    (finiteProbabilityMeasureBarycenter weights strategies).toFiniteMeasure =
      ∑ i, simplexWeightNNReal weights i • (strategies i).toFiniteMeasure := by
  apply MeasureTheory.FiniteMeasure.toMeasure_injective
  simp [finiteProbabilityMeasureBarycenter, MeasureTheory.FiniteMeasure.toMeasure_sum,
    MeasureTheory.FiniteMeasure.toMeasure_smul]

/-- Finite probability-measure barycenters vary continuously in their simplex weights. -/
theorem continuous_finiteProbabilityMeasureBarycenter
    {Action Index : Type*} [MeasurableSpace Action] [TopologicalSpace Action]
    [OpensMeasurableSpace Action] [Fintype Index]
    (strategies : Index → MeasureTheory.ProbabilityMeasure Action) :
    Continuous fun weights : stdSimplex ℝ Index =>
      finiteProbabilityMeasureBarycenter weights strategies := by
  refine (MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding Action).continuous_iff.mpr ?_
  change Continuous fun weights : stdSimplex ℝ Index =>
    (finiteProbabilityMeasureBarycenter weights strategies).toFiniteMeasure
  simp_rw [finiteProbabilityMeasureBarycenter_toFiniteMeasure]
  apply continuous_finset_sum Finset.univ
  intro i _
  have hweight : Continuous fun weights : stdSimplex ℝ Index =>
      simplexWeightNNReal weights i := by
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val
  exact hweight.smul continuous_const

/--
Mixed-extension payoff is affine in the player's own probability law.  The
integrability hypotheses are explicit because discontinuous pure payoffs need
not be integrable merely from their type.
-/
theorem mixedExtensionPayoff_probabilityMeasureMix
    {Action State : Type*} [MeasurableSpace Action]
    (payoff : Action → State → ℝ) (state : State) (weight : I)
    (left right : MeasureTheory.ProbabilityMeasure Action)
    (hleft : MeasureTheory.Integrable (fun action => payoff action state) left.toMeasure)
    (hright : MeasureTheory.Integrable (fun action => payoff action state) right.toMeasure) :
    MixedExtensionPayoff payoff (probabilityMeasureMix weight left right) state =
      (weight : ℝ) * MixedExtensionPayoff payoff left state +
        (1 - weight : ℝ) * MixedExtensionPayoff payoff right state := by
  unfold MixedExtensionPayoff
  rw [probabilityMeasureMix_toMeasure,
    MeasureTheory.integral_add_measure hleft.smul_measure_nnreal hright.smul_measure_nnreal,
    MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_smul_nnreal_measure]
  rfl

/--
Mixed-extension payoff is affine in an arbitrary finite probability-law
barycenter.  This is the finite-mixture form needed to verify the KKM cover
condition directly on a compact space of mixed actions.
-/
theorem mixedExtensionPayoff_finiteProbabilityMeasureBarycenter
    {Action State Index : Type*} [MeasurableSpace Action] [Fintype Index]
    (payoff : Action → State → ℝ) (state : State)
    (weights : stdSimplex ℝ Index)
    (strategies : Index → MeasureTheory.ProbabilityMeasure Action)
    (hintegrable : ∀ i,
      MeasureTheory.Integrable (fun action => payoff action state) (strategies i).toMeasure) :
    MixedExtensionPayoff payoff (finiteProbabilityMeasureBarycenter weights strategies) state =
      ∑ i, weights i * MixedExtensionPayoff payoff (strategies i) state := by
  unfold MixedExtensionPayoff
  rw [show (finiteProbabilityMeasureBarycenter weights strategies).toMeasure =
      ∑ i, simplexWeightNNReal weights i • (strategies i).toMeasure by
    rfl]
  rw [MeasureTheory.integral_finset_sum_measure]
  · simp_rw [MeasureTheory.integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, coe_simplexWeightNNReal, smul_eq_mul]
  · intro i _
    exact (hintegrable i).smul_measure_nnreal

/--
An affine finite barycenter has a member of its positive-weight support whose
payoff does not exceed the barycenter's diagonal payoff.  This is the KKM
cover condition for a mixed extension, derived from finite affinity rather
than postulated as a certificate.
-/
theorem exists_le_diagonal_of_finiteBarycenter_affine
    {Action Index : Type*} [Fintype Index] [Nonempty Index]
    (payoff : Action → Action → ℝ) (strategies : Index → Action)
    (barycenter : stdSimplex ℝ Index → Action)
    (haffine : ∀ weights : stdSimplex ℝ Index,
      payoff (barycenter weights) (barycenter weights) =
        ∑ i, weights i * payoff (strategies i) (barycenter weights))
    (weights : stdSimplex ℝ Index) :
    ∃ i, 0 < weights i ∧
      payoff (strategies i) (barycenter weights) ≤ payoff (barycenter weights) (barycenter weights) := by
  have hpositive : ∃ i, 0 < weights i := by
    by_contra h
    push Not at h
    have hzero : ∀ i, weights i = 0 := by
      intro i
      exact le_antisymm (h i) (stdSimplex.zero_le weights i)
    have hone : (1 : ℝ) = 0 := by
      rw [← stdSimplex.sum_eq_one weights]
      exact Finset.sum_eq_zero fun i _ => hzero i
    norm_num at hone
  by_contra hcover
  push Not at hcover
  have hstrict : ∀ i, 0 < weights i →
      payoff (barycenter weights) (barycenter weights) <
        payoff (strategies i) (barycenter weights) := by
    intro i hi
    exact hcover i hi
  have hterms : ∀ i,
      weights i * payoff (barycenter weights) (barycenter weights) ≤
        weights i * payoff (strategies i) (barycenter weights) := by
    intro i
    by_cases hi : 0 < weights i
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hstrict i hi))
        (stdSimplex.zero_le weights i)
    · have hzero : weights i = 0 := le_antisymm (le_of_not_gt hi) (stdSimplex.zero_le weights i)
      simp [hzero]
  obtain ⟨i, hi⟩ := hpositive
  have hterm_strict :
      weights i * payoff (barycenter weights) (barycenter weights) <
        weights i * payoff (strategies i) (barycenter weights) := by
    exact mul_lt_mul_of_pos_left (hstrict i hi) hi
  have hsum_strict :
      (∑ i, weights i * payoff (barycenter weights) (barycenter weights)) <
        ∑ i, weights i * payoff (strategies i) (barycenter weights) := by
    simpa using Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hterms i)
      ⟨i, Finset.mem_univ i, hterm_strict⟩
  have hdiag_sum :
      payoff (barycenter weights) (barycenter weights) =
        ∑ i, weights i * payoff (barycenter weights) (barycenter weights) := by
    rw [← Finset.sum_mul, stdSimplex.sum_eq_one weights, one_mul]
  have hcontradiction :
      payoff (barycenter weights) (barycenter weights) <
        payoff (barycenter weights) (barycenter weights) := by
    calc
      payoff (barycenter weights) (barycenter weights) =
          ∑ i, weights i * payoff (barycenter weights) (barycenter weights) := hdiag_sum
      _ < ∑ i, weights i * payoff (strategies i) (barycenter weights) := hsum_strict
      _ = payoff (barycenter weights) (barycenter weights) := (haffine weights).symm
  exact (lt_irrefl _) hcontradiction

/--
Quasi-concavity on a probability-law action space, expressed with its natural
binary affine mixtures.  This avoids pretending that probability measures form
a real vector space while retaining exactly the upper-contour convexity needed
by the discontinuous-game fixed-point route.
-/
def ProbabilityMeasureQuasiConcave {Action : Type*} [MeasurableSpace Action]
    (payoff : MeasureTheory.ProbabilityMeasure Action → ℝ) : Prop :=
  ∀ threshold left right, threshold ≤ payoff left → threshold ≤ payoff right →
    ∀ weight : I, threshold ≤ payoff (probabilityMeasureMix weight left right)

/-- Diagonal quasi-concavity for a payoff whose action and diagonal state are laws. -/
def DiagonallyProbabilityMeasureQuasiConcave {Action : Type*} [MeasurableSpace Action]
    (payoff : MeasureTheory.ProbabilityMeasure Action →
      MeasureTheory.ProbabilityMeasure Action → ℝ) : Prop :=
  ∀ state, ProbabilityMeasureQuasiConcave (fun action => payoff action state)

/--
An equilibrium of a one-action diagonal game: no action has payoff above the
diagonal action against that diagonal state.  This is the conclusion supplied
by a diagonal fixed-point theorem before any source-specific support semantics
are imposed.
-/
def IsDiagonalNash {Action : Type*} (payoff : Action → Action → ℝ)
    (state : Action) : Prop :=
  ∀ action, payoff action state ≤ payoff state state

/--
If a payoff is almost everywhere equal to `value`, every topological-support
action receives at least `value` when the payoff is upper semicontinuous.  A
separate global upper bound turns this into equality; this is the exact
regularity bridge needed to pass from a mixed-law best-response conclusion to
the stronger support-action equilibrium convention used by some source
papers.

Without upper semicontinuity the conclusion is false in general: a measure can
place mass arbitrarily near a downward jump of the payoff while the jump point
itself belongs to its topological support.
-/
theorem le_of_mem_support_of_ae_eq_of_upperSemicontinuous
    {Action : Type*} [TopologicalSpace Action] [MeasurableSpace Action]
    {measure : MeasureTheory.Measure Action} {payoff : Action → ℝ}
    {value : ℝ} {action : Action}
    (hsupport : action ∈ measure.support)
    (hae : ∀ᵐ action ∂measure, payoff action = value)
    (husc : UpperSemicontinuous payoff) :
    value ≤ payoff action := by
  have hnot_lt : ¬ payoff action < value := by
    intro hlt
    let threshold : ℝ := (payoff action + value) / 2
    have haction_lt : payoff action < threshold := by
      dsimp [threshold]
      linarith
    have hthreshold_lt : threshold < value := by
      dsimp [threshold]
      linarith
    have hneighborhood : payoff ⁻¹' Set.Iio threshold ∈ nhds action :=
      husc action threshold haction_lt
    have hpositive : 0 < measure (payoff ⁻¹' Set.Iio threshold) :=
      (MeasureTheory.Measure.mem_support_iff_forall action).mp hsupport _ hneighborhood
    have hnull_bad : measure {action | payoff action ≠ value} = 0 := by
      simpa only [Filter.eventually_iff] using hae
    have hsubset : payoff ⁻¹' Set.Iio threshold ⊆ {action | payoff action ≠ value} := by
      intro action haction
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq] at haction ⊢
      exact ne_of_lt (lt_trans haction hthreshold_lt)
    have hnull : measure (payoff ⁻¹' Set.Iio threshold) = 0 :=
      MeasureTheory.measure_mono_null hsubset hnull_bad
    exact (ne_of_gt hpositive) hnull
  exact le_of_not_gt hnot_lt

/--
A diagonal Nash law of a mixed extension rules out every pure deviation.  The
Dirac evaluation needs the displayed strong-measurability premise; it is not a
formal consequence of a discontinuous payoff's type.
-/
theorem IsDiagonalNash.purePayoff_le_mixedPayoff
    {Action : Type*} [MeasurableSpace Action]
    {purePayoff : Action → MeasureTheory.ProbabilityMeasure Action → ℝ}
    {state : MeasureTheory.ProbabilityMeasure Action}
    (hnash : IsDiagonalNash (MixedExtensionPayoff purePayoff) state)
    (hmeasurable : MeasureTheory.StronglyMeasurable (fun action => purePayoff action state))
    (action : Action) :
    purePayoff action state ≤ MixedExtensionPayoff purePayoff state state := by
  have h := hnash (MeasureTheory.diracProba action)
  change (∫ action', purePayoff action' state ∂MeasureTheory.Measure.dirac action) ≤
    MixedExtensionPayoff purePayoff state state at h
  simpa only [MeasureTheory.integral_dirac' _ _ hmeasurable] using h

/--
At a mixed-extension diagonal Nash law, the pure payoff equals the mixed
payoff almost everywhere under the equilibrium law.  This intentionally gives
an a.e. statement only: without an additional upper-semicontinuity or
support-regularity hypothesis, it cannot be strengthened to every point of the
topological support.
-/
theorem IsDiagonalNash.ae_purePayoff_eq_mixedPayoff
    {Action : Type*} [MeasurableSpace Action]
    {purePayoff : Action → MeasureTheory.ProbabilityMeasure Action → ℝ}
    {state : MeasureTheory.ProbabilityMeasure Action}
    (hnash : IsDiagonalNash (MixedExtensionPayoff purePayoff) state)
    (hmeasurable : MeasureTheory.StronglyMeasurable (fun action => purePayoff action state))
    (hintegrable : MeasureTheory.Integrable (fun action => purePayoff action state)
      state.toMeasure) :
    ∀ᵐ action ∂state.toMeasure,
      purePayoff action state = MixedExtensionPayoff purePayoff state state := by
  let value := MixedExtensionPayoff purePayoff state state
  have hconst : MeasureTheory.Integrable (fun _ : Action => value) state.toMeasure :=
    MeasureTheory.integrable_const _
  have hdiff : MeasureTheory.Integrable
      (fun action => value - purePayoff action state) state.toMeasure :=
    hconst.sub hintegrable
  have hnonneg : ∀ᵐ action ∂state.toMeasure, 0 ≤ value - purePayoff action state :=
    Filter.Eventually.of_forall fun action =>
      sub_nonneg.mpr (hnash.purePayoff_le_mixedPayoff hmeasurable action)
  have hmean_zero : ∫ action, value - purePayoff action state ∂state.toMeasure = 0 := by
    rw [MeasureTheory.integral_sub hconst hintegrable, MeasureTheory.integral_const]
    simp [value, MixedExtensionPayoff]
  have hzero : (fun action => value - purePayoff action state) =ᵐ[state.toMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hdiff).mp hmean_zero
  filter_upwards [hzero] with action haction
  dsimp [value] at haction ⊢
  linarith

/--
If a pure payoff against a fixed mixed law is upper semicontinuous, a diagonal
Nash law makes every topological-support action a best response.  This is a
corollary of the a.e. payoff identity, and intentionally keeps the
upper-semicontinuity premise explicit rather than treating it as automatic for
discontinuous games.
-/
theorem IsDiagonalNash.purePayoff_eq_mixedPayoff_of_mem_support_of_upperSemicontinuous
    {Action : Type*} [TopologicalSpace Action] [MeasurableSpace Action]
    {purePayoff : Action → MeasureTheory.ProbabilityMeasure Action → ℝ}
    {state : MeasureTheory.ProbabilityMeasure Action} {action : Action}
    (hnash : IsDiagonalNash (MixedExtensionPayoff purePayoff) state)
    (hmeasurable : MeasureTheory.StronglyMeasurable (fun action => purePayoff action state))
    (hintegrable : MeasureTheory.Integrable (fun action => purePayoff action state)
      state.toMeasure)
    (hsupport : action ∈ state.toMeasure.support)
    (husc : UpperSemicontinuous (fun action => purePayoff action state)) :
    purePayoff action state = MixedExtensionPayoff purePayoff state state := by
  apply le_antisymm
  · exact hnash.purePayoff_le_mixedPayoff hmeasurable action
  · exact le_of_mem_support_of_ae_eq_of_upperSemicontinuous
      (measure := state.toMeasure) (payoff := fun action => purePayoff action state)
      hsupport (hnash.ae_purePayoff_eq_mixedPayoff hmeasurable hintegrable) husc

/-- An integrable mixed extension is diagonally quasi-concave by affinity. -/
theorem mixedExtensionPayoff_diagonallyProbabilityMeasureQuasiConcave
    {Action : Type*} [MeasurableSpace Action]
    (payoff : Action → MeasureTheory.ProbabilityMeasure Action → ℝ)
    (hintegrable : ∀ state (strategy : MeasureTheory.ProbabilityMeasure Action),
      MeasureTheory.Integrable (fun action => payoff action state) strategy.toMeasure) :
    DiagonallyProbabilityMeasureQuasiConcave (MixedExtensionPayoff payoff) := by
  intro state threshold left right hleft hright weight
  change threshold ≤ MixedExtensionPayoff payoff (probabilityMeasureMix weight left right) state
    at ⊢
  rw [mixedExtensionPayoff_probabilityMeasureMix payoff state weight left right
    (hintegrable state left) (hintegrable state right)]
  have hweight_nonneg : 0 ≤ (weight : ℝ) := weight.2.1
  have hcomplement_nonneg : 0 ≤ (1 - weight : ℝ) := by linarith [weight.2.2]
  nlinarith [mul_nonneg hweight_nonneg (sub_nonneg.mpr hleft),
    mul_nonneg hcomplement_nonneg (sub_nonneg.mpr hright)]

/--
Lift corrected diagonal payoff security from pure deviations to the mixed
extension, provided every pure-action payoff is strongly measurable and
integrable under every mixed action.  The proof uses the elementary fact that
an integrable function under a probability law attains at least its integral
at one point, then embeds the pure securing action as a Dirac law.

The hypotheses are deliberately explicit: compactness alone does not make a
discontinuous payoff measurable, and the lift must not silently assume it.
-/
theorem PureDiagonalPayoffSecureOn.mixedExtension_diagonallyPayoffSecure
    {PureAction : Type*} [MeasurableSpace PureAction]
    [TopologicalSpace (MeasureTheory.ProbabilityMeasure PureAction)]
    {payoff : PureAction → MeasureTheory.ProbabilityMeasure PureAction → ℝ}
    (hsecure : PureDiagonalPayoffSecureOn Set.univ payoff)
    (hmeasurable : ∀ state, MeasureTheory.StronglyMeasurable (fun action => payoff action state))
    (hintegrable : ∀ state (strategy : MeasureTheory.ProbabilityMeasure PureAction),
      MeasureTheory.Integrable (fun action => payoff action state) strategy.toMeasure) :
    DiagonallyPayoffSecure (MixedExtensionPayoff payoff) := by
  intro state deviation ε hε
  obtain ⟨action, haction⟩ :=
    MeasureTheory.exists_integral_le (hintegrable state deviation)
  obtain ⟨securingAction, -, hsecuring⟩ :=
    hsecure state action (Set.mem_univ action) (ε / 2) (by linarith)
  refine ⟨MeasureTheory.diracProba securingAction, ?_⟩
  rcases hsecuring with ⟨U, hU, hpayoff⟩
  refine ⟨U, hU, ?_⟩
  intro state' hstate'
  have htarget :
      MixedExtensionPayoff payoff deviation state - ε ≤ payoff action state - ε / 2 := by
    unfold MixedExtensionPayoff
    linarith
  have hsecured : payoff action state - ε / 2 < payoff securingAction state' :=
    hpayoff state' hstate'
  change (∫ action, payoff action state ∂deviation.toMeasure) - ε <
    ∫ action, payoff action state' ∂(MeasureTheory.diracProba securingAction).toMeasure
  rw [show (MeasureTheory.diracProba securingAction).toMeasure =
      MeasureTheory.Measure.dirac securingAction from rfl,
    MeasureTheory.integral_dirac' _ _ (hmeasurable state')]
  exact lt_of_le_of_lt htarget hsecured

/--
Diagonal better-reply security: at every diagonal state admitting a strict
deviation, one action secures a payoff strictly above the diagonal payoff.
This is weaker than diagonal payoff security and is the local conclusion used
directly in the JGS source proof.
-/
def DiagonallyBetterReplySecure {Action : Type*} [TopologicalSpace Action]
    (payoff : Action → Action → ℝ) : Prop :=
  ∀ x : Action, (∃ y : Action, payoff x x < payoff y x) →
    ∃ securingAction : Action, ∃ value : ℝ,
      payoff x x < value ∧ SecuresPayoffAt payoff securingAction value x

/-- Corrected diagonal payoff security implies diagonal better-reply security. -/
theorem DiagonallyPayoffSecure.diagonallyBetterReplySecure
    {Action : Type*} [TopologicalSpace Action] {payoff : Action → Action → ℝ}
    (hsecure : DiagonallyPayoffSecure payoff) :
    DiagonallyBetterReplySecure payoff := by
  intro x hbetter
  rcases hbetter with ⟨y, hxy⟩
  let ε : ℝ := (payoff y x - payoff x x) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hsecure x y ε hε with ⟨securingAction, hsecuringAction⟩
  refine ⟨securingAction, payoff y x - ε, ?_, hsecuringAction⟩
  dsimp [ε]
  linarith

/--
A compact diagonal-continuous finite-barycentric game with local
better-reply security has a diagonal Nash state.  This is a proved KKM route
for compact mixed extensions.  It is deliberately stated with diagonal
continuity, a stronger premise than the upper/lower-envelope version of
Reny's general discontinuous-game theorem.
-/
theorem exists_isDiagonalNash_of_compact_barycentric
    {Action : Type*} [TopologicalSpace Action] [CompactSpace Action] [Nonempty Action]
    (payoff : Action → Action → ℝ)
    (hdiagonal : Continuous fun state => payoff state state)
    (hsecure : DiagonallyBetterReplySecure payoff)
    (hbarycenter : ∀ (s : Finset Action), s.Nonempty →
      ∃ barycenter : stdSimplex ℝ s → Action, Continuous barycenter ∧
        ∀ weights : stdSimplex ℝ s,
          ∃ action : s, 0 < weights action ∧
            payoff action (barycenter weights) ≤ payoff (barycenter weights) (barycenter weights)) :
    ∃ state, IsDiagonalNash payoff state := by
  let C : Action → Set Action := fun action =>
    closure {state | payoff action state ≤ payoff state state}
  have hclosed : ∀ action, IsClosed (C action) := by
    intro action
    exact isClosed_closure
  obtain ⟨state, hstate⟩ := compactKKM_barycentric C hclosed (by
    intro s hs
    obtain ⟨barycenter, hbarycenter_continuous, hcover⟩ := hbarycenter s hs
    refine ⟨barycenter, hbarycenter_continuous, ?_⟩
    intro weights
    obtain ⟨action, hpositive, hle⟩ := hcover weights
    exact ⟨action, hpositive, subset_closure hle⟩)
  refine ⟨state, ?_⟩
  intro action
  by_contra hnot
  have hbetter : payoff state state < payoff action state := lt_of_not_ge hnot
  obtain ⟨securingAction, value, hvalue, hsecuring⟩ := hsecure state ⟨action, hbetter⟩
  rcases hsecuring with ⟨U, hU, hpayoff⟩
  have hV : {state' | payoff state' state' < value} ∈ nhds state := by
    exact hdiagonal.continuousAt.eventually_lt continuousAt_const hvalue
  have hclosure : state ∈ C securingAction := hstate securingAction
  obtain ⟨state', hstate'U, hstate'failure⟩ :=
    (mem_closure_iff_nhds.mp hclosure) (U ∩ {state' | payoff state' state' < value})
      (Filter.inter_mem hU hV)
  have hsecured : value < payoff securingAction state' := hpayoff state' hstate'U.1
  have hdiagonal_lt : payoff state' state' < value := hstate'U.2
  exact (not_lt_of_ge hstate'failure) (hdiagonal_lt.trans hsecured)

end AppliedModelingLib

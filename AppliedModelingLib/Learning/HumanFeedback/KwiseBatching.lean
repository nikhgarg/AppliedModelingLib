import AppliedModelingLib.Learning.HumanFeedback.PlackettLuce
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Algebra.Order.Floor.Div

/-!
# Independent pair batching from ranking queries

One ranking query on `rankingSize` items exposes at most
`floor (rankingSize / 2)` disjoint ordered pairs.  This module keeps the exact
natural-number batching arithmetic and an explicit probabilistic interface
for the disjoint-pair independence property.  Plackett--Luce internal
consistency can instantiate that interface; the independence theorem itself
is an attributed ranking-model result, not silently reproved here.
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

noncomputable section

open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory

/-- Number of disjoint pairs available in one ranking of `rankingSize` items. -/
def disjointPairCapacity (rankingSize : ℕ) : ℕ := rankingSize / 2

/--
Exact number of ranking calls needed to expose `pairCount` disjoint pairs,
using ceiling division and totalizing to zero if the ranking has size below
two.
-/
def rankingBatchQueryCount (rankingSize pairCount : ℕ) : ℕ :=
  pairCount ⌈/⌉ disjointPairCapacity rankingSize

/--
One ranking outcome supplies an independent vector of pairwise observations
with the specified common law.  Equality to `pmfProduct` records both the
correct Bernoulli marginal and mutual independence, rather than only matching
expectations.
-/
structure IndependentDisjointPairBatch
    (Outcome PairObservation : Type*) [Fintype PairObservation]
    (capacity : ℕ) where
  outcomeLaw : PMF Outcome
  pairLaw : PMF PairObservation
  observe : Outcome → Fin capacity → PairObservation
  jointLaw_eq_product :
    outcomeLaw.map (fun outcome pair ↦ observe outcome pair) =
      pmfProduct (Fin capacity) PairObservation pairLaw

/--
Every observed disjoint pair has the batch's specified marginal law.  The
product-law field makes this a derived fact rather than an additional
assumption.
-/
theorem IndependentDisjointPairBatch.toMeasure_map_observe_eq_pairLaw
    {Outcome PairObservation : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype PairObservation] [DecidableEq PairObservation]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    [MeasurableSpace PairObservation] [DiscreteMeasurableSpace PairObservation]
    {capacity : ℕ}
    (batch : IndependentDisjointPairBatch Outcome PairObservation capacity)
    (pair : Fin capacity) :
    batch.outcomeLaw.toMeasure.map (fun outcome => batch.observe outcome pair) =
      batch.pairLaw.toMeasure := by
  calc
    batch.outcomeLaw.toMeasure.map (fun outcome => batch.observe outcome pair) =
        (batch.outcomeLaw.map (fun outcome => batch.observe outcome pair)).toMeasure :=
      PMF.toMeasure_map _ _ (measurable_of_finite _)
    _ = ((batch.outcomeLaw.map (fun outcome point => batch.observe outcome point)).map
        (fun sample => sample pair)).toMeasure := by
      congr 1
      rw [PMF.map_comp]
      rfl
    _ = ((pmfProduct (Fin capacity) PairObservation batch.pairLaw).map
        (fun sample => sample pair)).toMeasure := by
      rw [batch.jointLaw_eq_product]
    _ = (pmfProduct (Fin capacity) PairObservation batch.pairLaw).toMeasure.map
        (fun sample => sample pair) :=
      (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm
    _ = (Measure.pi (fun _ : Fin capacity => batch.pairLaw.toMeasure)).map
        (fun sample => sample pair) := by
      rw [pmfProduct_toMeasure_eq_measurePi]
    _ = batch.pairLaw.toMeasure := by
      rw [Measure.pi_map_eval]
      simp

/--
The product-law field in `IndependentDisjointPairBatch` has its intended
probabilistic content: all observed disjoint-pair labels are mutually
independent under the ranking outcome law.  The source-specific task of
establishing that product-law field for Plackett--Luce rankings remains an
explicit attributed premise.
-/
theorem IndependentDisjointPairBatch.iIndepFun_observe
    {Outcome PairObservation : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype PairObservation] [DecidableEq PairObservation]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    [MeasurableSpace PairObservation] [DiscreteMeasurableSpace PairObservation]
    {capacity : ℕ}
    (batch : IndependentDisjointPairBatch Outcome PairObservation capacity) :
    iIndepFun (fun pair : Fin capacity => fun outcome => batch.observe outcome pair)
      batch.outcomeLaw.toMeasure := by
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun _ => (measurable_of_finite _).aemeasurable)]
  calc
    batch.outcomeLaw.toMeasure.map (fun outcome pair => batch.observe outcome pair) =
        (batch.outcomeLaw.map (fun outcome pair => batch.observe outcome pair)).toMeasure :=
      PMF.toMeasure_map _ _ (measurable_of_finite _)
    _ = (pmfProduct (Fin capacity) PairObservation batch.pairLaw).toMeasure := by
      rw [batch.jointLaw_eq_product]
    _ = Measure.pi (fun _ : Fin capacity => batch.pairLaw.toMeasure) := by
      rw [pmfProduct_toMeasure_eq_measurePi]
    _ = Measure.pi (fun pair =>
        batch.outcomeLaw.toMeasure.map (fun outcome => batch.observe outcome pair)) := by
      congr 1
      funext pair
      exact (batch.toMeasure_map_observe_eq_pairLaw pair).symm

/--
Selecting distinct pair coordinates from a product-law ranking batch preserves
their complete product law.  This is stronger than retaining only their
marginals: it permits a large K-wise ranking to supply exactly the requested
number of P2R repetitions while safely ignoring unused disjoint pairs.
-/
theorem IndependentDisjointPairBatch.map_observe_precomp_eq_pmfProduct
    {Outcome PairObservation : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype PairObservation] [DecidableEq PairObservation]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    [MeasurableSpace PairObservation] [DiscreteMeasurableSpace PairObservation]
    {capacity selected : ℕ}
    (batch : IndependentDisjointPairBatch Outcome PairObservation capacity)
    (selection : Fin selected → Fin capacity) (hselection : Function.Injective selection) :
    batch.outcomeLaw.map (fun outcome pair => batch.observe outcome (selection pair)) =
      pmfProduct (Fin selected) PairObservation batch.pairLaw := by
  apply PMF.toMeasure_injective
  have hselected :
      iIndepFun (fun pair : Fin selected => fun outcome =>
        batch.observe outcome (selection pair)) batch.outcomeLaw.toMeasure :=
    batch.iIndepFun_observe.precomp hselection
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun _ => (measurable_of_finite _).aemeasurable)] at hselected
  calc
    (batch.outcomeLaw.map (fun outcome pair =>
        batch.observe outcome (selection pair))).toMeasure =
        batch.outcomeLaw.toMeasure.map (fun outcome pair =>
          batch.observe outcome (selection pair)) :=
      (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm
    _ = Measure.pi (fun pair =>
        batch.outcomeLaw.toMeasure.map (fun outcome =>
          batch.observe outcome (selection pair))) := hselected
    _ = Measure.pi (fun _ : Fin selected => batch.pairLaw.toMeasure) := by
      congr 1
      funext pair
      exact batch.toMeasure_map_observe_eq_pairLaw (selection pair)
    _ = (pmfProduct (Fin selected) PairObservation batch.pairLaw).toMeasure := by
      rw [pmfProduct_toMeasure_eq_measurePi]

/--
The observable subbatch obtained by retaining any distinct set of pairs from
a ranking batch.  Its product law is derived by
`map_observe_precomp_eq_pmfProduct`, so no new independence assumption is
introduced by the restriction.
-/
noncomputable def IndependentDisjointPairBatch.restrict
    {Outcome PairObservation : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [Fintype PairObservation] [DecidableEq PairObservation]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    [MeasurableSpace PairObservation] [DiscreteMeasurableSpace PairObservation]
    {capacity selected : ℕ}
    (batch : IndependentDisjointPairBatch Outcome PairObservation capacity)
    (selection : Fin selected → Fin capacity) (hselection : Function.Injective selection) :
    IndependentDisjointPairBatch Outcome PairObservation selected where
  outcomeLaw := batch.outcomeLaw
  pairLaw := batch.pairLaw
  observe := fun outcome pair => batch.observe outcome (selection pair)
  jointLaw_eq_product := batch.map_observe_precomp_eq_pmfProduct selection hselection

/--
The finite observable-label outcome shape for the ceiling-divided K-wise
batching schedule.  It has one coordinate for each ranking call and each
usable disjoint pair inside that call.
-/
abbrev KwiseLabelTape (rankingSize repetitions : ℕ) (PairObservation : Type*) :=
  (Fin (rankingBatchQueryCount rankingSize repetitions) ×
    Fin (disjointPairCapacity rankingSize)) → PairObservation

/--
The observed-label law of a prescribed number of fresh K-wise ranking calls.
Only the disjoint-pair labels are retained: each call contributes `capacity`
independent coordinates and different calls are sampled freshly.  This is the
finite operational form of the ordinary oracle-call semantics used when the
same P2R comparison needs more labels than fit in one ranking.
-/
noncomputable def freshKwiseLabelTapeLaw
    (rankingCalls capacity : ℕ) {PairObservation : Type*}
    [Fintype PairObservation] [DecidableEq PairObservation]
    (pairLaw : PMF PairObservation) :
    PMF ((Fin rankingCalls × Fin capacity) → PairObservation) :=
  pmfProduct (Fin rankingCalls × Fin capacity) PairObservation pairLaw

/-- The first `requested` cells of a K-wise label tape, in call-major order. -/
noncomputable def freshKwiseLabelTapeSelection
    {rankingCalls capacity requested : ℕ}
    (hcover : requested ≤ rankingCalls * capacity) :
    Fin requested → Fin rankingCalls × Fin capacity :=
  fun requestedIndex =>
    finProdFinEquiv.symm (Fin.castLE hcover requestedIndex)

theorem freshKwiseLabelTapeSelection_injective
    {rankingCalls capacity requested : ℕ}
    (hcover : requested ≤ rankingCalls * capacity) :
    Function.Injective (freshKwiseLabelTapeSelection hcover) :=
  finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hcover)

/--
The first `requested` labels of a fresh K-wise tape form an independent batch
with exactly the requested common pair law.  This construction proves the
small-K multi-ranking composition at the observable-label level; it does not
identify a Plackett--Luce ranking with the product law, which remains the
separate Property-8 source obligation.
-/
noncomputable def freshKwiseRepeatedPairBatch
    {PairObservation : Type*} [Fintype PairObservation] [DecidableEq PairObservation]
    [MeasurableSpace PairObservation] [DiscreteMeasurableSpace PairObservation]
    {rankingCalls capacity requested : ℕ}
    (pairLaw : PMF PairObservation)
    (hcover : requested ≤ rankingCalls * capacity) :
    IndependentDisjointPairBatch
      ((Fin rankingCalls × Fin capacity) → PairObservation) PairObservation requested where
  outcomeLaw := freshKwiseLabelTapeLaw rankingCalls capacity pairLaw
  pairLaw := pairLaw
  observe := fun tape requestedIndex => tape (freshKwiseLabelTapeSelection hcover requestedIndex)
  jointLaw_eq_product := by
    exact pmfProduct_map_precomp_eq_pmfProduct_of_injective pairLaw
      (freshKwiseLabelTapeSelection hcover)
      (freshKwiseLabelTapeSelection_injective hcover)

/--
For binary pair observations, the same product-law interface supplies the
real-valued independent family consumed by finite Hoeffding bounds.
-/
theorem IndependentDisjointPairBatch.iIndepFun_observeBoolCoe
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {capacity : ℕ}
    (batch : IndependentDisjointPairBatch Outcome Bool capacity) :
    iIndepFun (fun pair : Fin capacity => fun outcome =>
      if batch.observe outcome pair then (1 : ℝ) else 0) batch.outcomeLaw.toMeasure := by
  simpa [Function.comp_def] using
    batch.iIndepFun_observe.comp
      (fun _ observation => if observation then (1 : ℝ) else 0)
      (fun _ => measurable_of_finite _)

/--
If the batch's binary marginal is Bernoulli with parameter `probability`, each
observed pair has that literal real-valued expectation.  This is derived from
the product-law interface, not assumed as a separate moment condition.
-/
theorem IndependentDisjointPairBatch.integral_observeBoolCoe_eq
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {capacity : ℕ}
    (batch : IndependentDisjointPairBatch Outcome Bool capacity)
    (probability : NNReal) (hprobability : probability ≤ 1)
    (hpairLaw : batch.pairLaw = PMF.bernoulli probability hprobability)
    (pair : Fin capacity) :
    batch.outcomeLaw.toMeasure[fun outcome =>
      if batch.observe outcome pair then (1 : ℝ) else 0] =
      (probability : ℝ) := by
  calc
    batch.outcomeLaw.toMeasure[fun outcome =>
        if batch.observe outcome pair then (1 : ℝ) else 0] =
        ∫ observation : Bool, if observation then (1 : ℝ) else 0 ∂
          batch.outcomeLaw.toMeasure.map (fun outcome => batch.observe outcome pair) := by
      rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
        (measurable_of_finite _).aestronglyMeasurable]
    _ = ∫ observation : Bool, if observation then (1 : ℝ) else 0 ∂batch.pairLaw.toMeasure := by
      rw [batch.toMeasure_map_observe_eq_pairLaw pair]
    _ = ∫ observation : Bool, if observation then (1 : ℝ) else 0 ∂
          (PMF.bernoulli probability hprobability).toMeasure := by
      rw [hpairLaw]
    _ = (probability : ℝ) := by
      simpa [Bool.cond_eq_ite] using (PMF.bernoulli_expectation hprobability)

/--
One K-wise ranking's disjoint binary labels satisfy the exact finite
Hoeffding upper-tail premise used by the P2R repeated-comparison analysis.
The bound is over the actual ranking-outcome law; no replacement by a scalar
IID sequence is made in the statement.
-/
theorem IndependentDisjointPairBatch.centeredPairSum_upperTail
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {capacity : ℕ}
    (batch : IndependentDisjointPairBatch Outcome Bool capacity)
    (error : ℝ) (herror : 0 ≤ error) :
    batch.outcomeLaw.toMeasure.real {outcome |
      (capacity : ℝ) * error ≤
        ∑ pair : Fin capacity,
          ((if batch.observe outcome pair then (1 : ℝ) else 0) -
            batch.outcomeLaw.toMeasure[fun sample =>
              if batch.observe sample pair then (1 : ℝ) else 0])} ≤
      Real.exp (-((capacity : ℝ) * error) ^ 2 /
        (2 * (capacity : ℝ) * (1 / 4 : ℝ))) := by
  simpa using
    PreferenceRL.iIndepBoundedObservation_centeredSum_upperTail_finset
      batch.outcomeLaw.toMeasure
      (fun pair outcome => if batch.observe outcome pair then (1 : ℝ) else 0)
      batch.iIndepFun_observeBoolCoe Finset.univ
      (by intro _ _; exact measurable_of_finite _)
      (by
        intro pair _
        exact Filter.Eventually.of_forall fun outcome => by
          by_cases h : batch.observe outcome pair = true <;> simp [h])
      error herror

/--
The empirical mean of all disjoint binary labels in one ranking has the same
two-sided Hoeffding tail as `capacity` independent pairwise comparison calls,
with its Bernoulli mean derived from the batch marginal law.
-/
theorem IndependentDisjointPairBatch.empiricalPairMean_hoeffding
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {capacity : ℕ}
    (batch : IndependentDisjointPairBatch Outcome Bool capacity)
    (probability : NNReal) (hprobability : probability ≤ 1)
    (hpairLaw : batch.pairLaw = PMF.bernoulli probability hprobability)
    (error : ℝ) (hcapacity : 0 < capacity) (herror : 0 ≤ error) :
    batch.outcomeLaw.toMeasure.real {outcome | error ≤
      |(∑ pair : Fin capacity,
          if batch.observe outcome pair then (1 : ℝ) else 0) / (capacity : ℝ) -
        (probability : ℝ)|} ≤
      2 * Real.exp (-2 * (capacity : ℝ) * error ^ 2) := by
  let observation : Fin capacity → Outcome → ℝ :=
    fun pair outcome => if batch.observe outcome pair then 1 else 0
  have hconcentration :=
    PreferenceRL.iIndepBoundedObservation_centeredSum_abs_upperTail_finset
      batch.outcomeLaw.toMeasure observation batch.iIndepFun_observeBoolCoe Finset.univ
      (by intro _ _; exact measurable_of_finite _)
      (by
        intro pair _
        exact Filter.Eventually.of_forall fun outcome => by
          by_cases h : batch.observe outcome pair = true <;> simp [observation, h])
      error herror
  have hmean : ∀ pair : Fin capacity,
      batch.outcomeLaw.toMeasure[observation pair] = (probability : ℝ) := by
    intro pair
    simpa [observation] using
      batch.integral_observeBoolCoe_eq probability hprobability hpairLaw pair
  have hsum : ∀ outcome,
      (∑ pair : Fin capacity,
        (observation pair outcome - batch.outcomeLaw.toMeasure[observation pair])) =
        ∑ pair : Fin capacity, (observation pair outcome - (probability : ℝ)) := by
    intro outcome
    apply Finset.sum_congr rfl
    intro pair _
    rw [hmean pair]
  have hsum_sub : ∀ outcome,
      (∑ pair : Fin capacity, (observation pair outcome - (probability : ℝ))) =
        (∑ pair : Fin capacity, observation pair outcome) -
          (capacity : ℝ) * probability := by
    intro outcome
    rw [Finset.sum_sub_distrib]
    simp [nsmul_eq_mul]
  have hcapacityReal : 0 < (capacity : ℝ) := by
    exact_mod_cast hcapacity
  have hevent : {outcome | error ≤
      |(∑ pair : Fin capacity, observation pair outcome) / (capacity : ℝ) -
        (probability : ℝ)|} =
      {outcome | (capacity : ℝ) * error ≤
        |∑ pair : Fin capacity,
          (observation pair outcome - batch.outcomeLaw.toMeasure[observation pair])|} := by
    ext outcome
    simp only [Set.mem_setOf_eq, hsum, hsum_sub]
    have hdivision :
        (∑ pair : Fin capacity, observation pair outcome) / (capacity : ℝ) -
            (probability : ℝ) =
          ((∑ pair : Fin capacity, observation pair outcome) -
            (capacity : ℝ) * probability) / (capacity : ℝ) := by
      field_simp
    rw [hdivision, abs_div, abs_of_pos hcapacityReal]
    simpa [mul_comm] using
      (le_div_iff₀ hcapacityReal :
        error ≤ |(∑ pair : Fin capacity, observation pair outcome) -
          (capacity : ℝ) * probability| / (capacity : ℝ) ↔
        error * (capacity : ℝ) ≤ |(∑ pair : Fin capacity, observation pair outcome) -
          (capacity : ℝ) * probability|)
  rw [hevent]
  calc
    batch.outcomeLaw.toMeasure.real {outcome | (capacity : ℝ) * error ≤
        |∑ pair : Fin capacity,
          (observation pair outcome - batch.outcomeLaw.toMeasure[observation pair])|} ≤
        2 * Real.exp (-((capacity : ℝ) * error) ^ 2 /
          (2 * (capacity : ℝ) * (1 / 4 : ℝ))) := by
            simpa [observation] using hconcentration
    _ = 2 * Real.exp (-2 * (capacity : ℝ) * error ^ 2) := by
      congr 2
      field_simp [ne_of_gt hcapacityReal]
      ring

/-- Rankings of size at least two have positive disjoint-pair capacity. -/
theorem disjointPairCapacity_pos {rankingSize : ℕ} (hsize : 2 ≤ rankingSize) :
    0 < disjointPairCapacity rankingSize := by
  unfold disjointPairCapacity
  exact Nat.div_pos (by omega) (by norm_num)

/-- The ceiling-divided number of queries exposes at least the requested pairs. -/
theorem pairCount_le_capacity_mul_rankingBatchQueryCount
    {rankingSize pairCount : ℕ} (hsize : 2 ≤ rankingSize) :
    pairCount ≤ disjointPairCapacity rankingSize *
      rankingBatchQueryCount rankingSize pairCount := by
  exact le_smul_ceilDiv (disjointPairCapacity_pos hsize)

/--
Ceiling batching packages exactly `repetitions` fresh pair labels into the
minimum number of K-wise ranking calls permitted by the disjoint-pair
capacity.  The construction is total only after the source's natural
`rankingSize ≥ 2` condition makes that capacity positive.
-/
noncomputable def kwiseRepeatedPairBatch
    {PairObservation : Type*} [Fintype PairObservation] [DecidableEq PairObservation]
    [MeasurableSpace PairObservation] [DiscreteMeasurableSpace PairObservation]
    (rankingSize repetitions : ℕ) (hsize : 2 ≤ rankingSize)
    (pairLaw : PMF PairObservation) :
    IndependentDisjointPairBatch
      (KwiseLabelTape rankingSize repetitions PairObservation)
      PairObservation repetitions := by
  let hcover : repetitions ≤
      rankingBatchQueryCount rankingSize repetitions * disjointPairCapacity rankingSize := by
    simpa [Nat.mul_comm] using
      (pairCount_le_capacity_mul_rankingBatchQueryCount
        (rankingSize := rankingSize) (pairCount := repetitions) hsize)
  exact freshKwiseRepeatedPairBatch pairLaw hcover

/-- The exact batching count is `(m + floor(K/2) - 1) / floor(K/2)`. -/
theorem rankingBatchQueryCount_eq_add_pred_div
    (rankingSize pairCount : ℕ) :
    rankingBatchQueryCount rankingSize pairCount =
      (pairCount + disjointPairCapacity rankingSize - 1) /
        disjointPairCapacity rankingSize := by
  exact Nat.ceilDiv_eq_add_pred_div _ _

/-- With at least two ranked items, batching never uses more calls than pairs. -/
theorem rankingBatchQueryCount_le_pairCount
    {rankingSize pairCount : ℕ} (hsize : 2 ≤ rankingSize) :
    rankingBatchQueryCount rankingSize pairCount ≤ pairCount := by
  apply (ceilDiv_le_iff_le_mul (disjointPairCapacity_pos hsize)).2
  have hcapacity : 1 ≤ disjointPairCapacity rankingSize :=
    disjointPairCapacity_pos hsize
  exact Nat.le_mul_of_pos_left pairCount hcapacity

/-- If `rankingSize ≥ 2 * pairCount`, all requested pairs fit in one query. -/
theorem rankingBatchQueryCount_le_one_of_two_mul_le
    {rankingSize pairCount : ℕ} (hsize : 2 ≤ rankingSize)
    (hfit : 2 * pairCount ≤ rankingSize) :
    rankingBatchQueryCount rankingSize pairCount ≤ 1 := by
  apply (ceilDiv_le_iff_le_mul (disjointPairCapacity_pos hsize)).2
  simp only [mul_one]
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by
    simpa [mul_comm] using hfit)

/-- A positive requested pair count cannot be served with zero ranking calls. -/
theorem rankingBatchQueryCount_pos
    {rankingSize pairCount : ℕ} (hsize : 2 ≤ rankingSize)
    (hpairs : 0 < pairCount) :
    0 < rankingBatchQueryCount rankingSize pairCount := by
  by_contra hzero
  have hqueryZero : rankingBatchQueryCount rankingSize pairCount = 0 :=
    Nat.eq_zero_of_not_pos hzero
  have hcover := pairCount_le_capacity_mul_rankingBatchQueryCount
    (rankingSize := rankingSize) (pairCount := pairCount) hsize
  rw [hqueryZero, mul_zero] at hcover
  omega

/--
Across `outerCount` comparison sites, exact K-wise batching needs the outer
count times the ceiling-divided repetitions per site.
-/
def totalRankingBatchQueryCount
    (outerCount rankingSize repetitions : ℕ) : ℕ :=
  outerCount * rankingBatchQueryCount rankingSize repetitions

/-- The batched budget supplies every requested repeated pair observation. -/
theorem totalPairObservations_le_totalBatchCapacity
    {outerCount rankingSize repetitions : ℕ} (hsize : 2 ≤ rankingSize) :
    outerCount * repetitions ≤
      totalRankingBatchQueryCount outerCount rankingSize repetitions *
        disjointPairCapacity rankingSize := by
  unfold totalRankingBatchQueryCount
  have hcover := pairCount_le_capacity_mul_rankingBatchQueryCount
    (rankingSize := rankingSize) (pairCount := repetitions) hsize
  nlinarith

end

end HumanFeedback
end Learning
end AppliedModelingLib

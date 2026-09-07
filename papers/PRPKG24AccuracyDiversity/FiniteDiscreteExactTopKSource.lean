import PRPKG24AccuracyDiversity.AppendixD1Source
import PRPKG24AccuracyDiversity.SourcePreferenceMixture

/-!
# Finite-discrete exact top-k source bridge

The finite optimizer development uses an at-most-`k` maximization primitive.
For the source model, Definition 3 instead sums exactly the `min k a` largest
conditional values.  These agree when conditional values are nonnegative;
this module makes that convention and the preferred-type PMF explicit.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

open AppliedModelingLib

/--
For a nonnegative finite iid value law, the optimizer's at-most-`k` count
value is the source's expected exact top-`k` sample sum.
-/
theorem finiteDiscreteIidTopKExpected_eq_expected_exactTopK
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (itemLaw : PMF Omega) (k : ℕ) (value : Omega → ℝ) (a : ℕ)
    (hvalue_nonneg : ∀ omega, 0 ≤ value omega) :
    finiteDiscreteIidTopKExpected Omega itemLaw k value a =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Fin a) Omega itemLaw)
        (fun sample : Fin a → Omega =>
          AppliedModelingLib.Probability.sampleTopKSum
            (fun i => value (sample i)) k) := by
  unfold finiteDiscreteIidTopKExpected iidTopKExpectedOn
  refine AppliedModelingLib.pmfExp_congr _ ?_
  intro sample
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    (AppliedModelingLib.Probability.topKSumOn_eq_sampleTopKSum_of_forall_nonneg
      (fun i => value (sample i)) k (fun i => hvalue_nonneg (sample i)))

/--
The finite-discrete conditional iid values, combined with the source's PMF
over preferred types, realize Equation (3) as the two-stage source
experiment.  No cross-type independence is asserted or needed.
-/
theorem finiteDiscreteIidTopKModel_objective_eq_source_experiment
    {T : ℕ} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (preferenceLaw : SourcePreferenceLaw T)
    (itemLaw : PMF Omega) (k : ℕ) (value : Omega → ℝ)
    (a : CountAllocation T)
    (hvalue_nonneg : ∀ omega, 0 ≤ value omega) :
    ((TopKValueOracle.common T
      (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
        (fun t => (preferenceLaw t).toReal) k).objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun _t =>
          AppliedModelingLib.pmfExp
            (AppliedModelingLib.pmfProduct (Fin (a.count _t)) Omega itemLaw)
            (fun sample : Fin (a.count _t) → Omega =>
              AppliedModelingLib.Probability.sampleTopKSum
                (fun i => value (sample i)) k)) := by
  let M : ConsumptionModel T :=
    (TopKValueOracle.common T
      (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
        (fun t => (preferenceLaw t).toReal) k
  calc
    M.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t => M.valueOfCount t (a.count t)) :=
      ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp M a
        preferenceLaw (by intro t; rfl)
    _ =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (AppliedModelingLib.pmfProduct (Fin (a.count t)) Omega itemLaw)
              (fun sample : Fin (a.count t) → Omega =>
                AppliedModelingLib.Probability.sampleTopKSum
                  (fun i => value (sample i)) k)) := by
      refine AppliedModelingLib.pmfExp_congr preferenceLaw ?_
      intro t
      simpa [M, TopKValueOracle.toConsumptionModel,
        TopKValueOracle.common_expectedTopSum] using
        finiteDiscreteIidTopKExpected_eq_expected_exactTopK
          itemLaw k value (a.count t) hvalue_nonneg

/--
Source-shaped Theorem 1(i) endpoint.  It explicitly packages the exact
top-`k` conditional experiment, the preferred-type PMF interpretation of
Equation (3), and the source's uniform asymptotic conclusion.
-/
theorem theorem1_i_finiteDiscrete_iid_exact_source_formula
    {T : ℕ} [NeZero T] {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (preferenceLaw : SourcePreferenceLaw T)
    (itemLaw : PMF Omega) (value : Omega → ℝ) {xTop xSecond : ℝ}
    (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
              (fun t => (preferenceLaw t).toReal) k))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_nonneg : ∀ omega, 0 ≤ value omega)
    (hvalue_le : ∀ omega, value omega ≤ xTop)
    (hvalue_split : ∀ omega, value omega = xTop ∨ value omega ≤ xSecond)
    (htop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => value omega = xTop))
    (hnontop_mass_pos :
      0 < AppliedModelingLib.pmfProb itemLaw (fun omega => ¬ value omega = xTop))
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal) :
    (∀ a : CountAllocation T,
      ((TopKValueOracle.common T
        (finiteDiscreteIidTopKExpected Omega itemLaw k value)).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun _t =>
            AppliedModelingLib.pmfExp
              (AppliedModelingLib.pmfProduct (Fin (a.count _t)) Omega itemLaw)
              (fun sample : Fin (a.count _t) → Omega =>
                AppliedModelingLib.Probability.sampleTopKSum
                  (fun i => value (sample i)) k))) ∧
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop (nhds (1 / (T : ℝ))) := by
  constructor
  · intro a
    exact finiteDiscreteIidTopKModel_objective_eq_source_experiment
      preferenceLaw itemLaw k value a hvalue_nonneg
  · exact lemmaD1_i_finiteDiscrete_iid_source_uniform_formula
      itemLaw value (fun t => (preferenceLaw t).toReal) k seq
      hk_pos hxTop_pos hxSecond_nonneg hsecond_le_top hsecond_lt_top
      hvalue_le hvalue_split htop_mass_pos hnontop_mass_pos hpreference_pos

end PRPKG24AccuracyDiversity

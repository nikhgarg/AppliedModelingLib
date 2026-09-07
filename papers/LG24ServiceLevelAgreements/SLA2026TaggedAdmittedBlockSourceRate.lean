import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastRate
import LG24ServiceLevelAgreements.SLA2026GPSParameters
import LG24ServiceLevelAgreements.SLA2026TargetPalmPastRenewalReward
import Mathlib.Tactic

/-!
# Aggregate past source-work rate for the SLA tagged input

This module keeps the direct target-Palm stream and every independently
stationary passive stream on their literal source carriers.  It records their
total marked work in the half-open physical-time window `[-t, 0)` and proves
only its source-input rate and the resulting aggregate negative net-work
drift under the source's GPS slack assumptions.

There is no merged global arrival index, queue state, reset, stationarity, or
response/tail conclusion here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Literal total admitted source work in the physical-time window `[-t, 0)`.
The target Palm arrival at zero is excluded by the target ledger's half-open
endpoint convention, and each passive coordinate uses its own literal
stationary arrival ledger. -/
def stationaryAdmittedTargetPassivePastAggregateWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (t : Real) : Real :=
  stationaryAdmittedTargetPalmPastWindowLedgerWork target z t +
    Finset.univ.sum (fun k : PassiveCategory target =>
      stationaryPoissonWorkPastAggregate (z.2 k) t)

/-- The literal total work in the unit half-open past block
`[-(n + 1), -n)`.  It is kept in direct ledger form rather than represented
through a merged event enumeration. -/
def stationaryAdmittedTargetPassivePastUnitBlockWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) : Real :=
  let a : Real := -((n : Real) + 1)
  let b : Real := -(n : Real)
  (palmTaggedArrivalIndices a b z.1.1).sum (fun i => z.1.2 i) +
    Finset.univ.sum (fun k : PassiveCategory target =>
      (suspensionBaseArrivalIndices a b (z.2 k).1).sum
        (stationaryPoissonWorkRequirement (z.2 k)))

/-- Every passive coordinate retains the direct stationary marked-Poisson
past-work rate after target-Palm recentering. -/
theorem ae_tendsto_stationaryAdmittedPassivePastAggregateWork_div_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (k : PassiveCategory target) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real => stationaryPoissonWorkPastAggregate (z.2 k) t / t)
        atTop (nhds (M.admittedRate k.1)) := by
  let targetTag := M.stationaryAdmittedTargetTaggedArrivalAtZero target
  let passiveBase := M.stationaryAdmittedPassiveBaseLaw target
  let rate : PassiveCategory target -> Real := fun j => M.admittedRate j.1
  letI : IsProbabilityMeasure targetTag.Ptag := targetTag.isProbability
  letI : IsProbabilityMeasure passiveBase.Pbase := passiveBase.isProbability
  have hcoordinate : MeasurePreserving (Function.eval k)
      passiveBase.Pbase (stationaryPoissonWorkMeasure (M.admittedRate k.1)) := by
    simpa [passiveBase, rate, stationaryAdmittedPassiveBaseLaw] using
      (measurePreserving_multiclassStationaryPoissonWorkPath rate
        (fun j => M.admittedRate_pos j.1) k)
  have hpassive : ∀ᵐ x ∂passiveBase.Pbase,
      Tendsto (fun t : Real => stationaryPoissonWorkPastAggregate (x k) t / t)
        atTop (nhds (M.admittedRate k.1)) := by
    refine ae_of_ae_map (μ := passiveBase.Pbase) (f := Function.eval k)
      (p := fun x : StationaryAdmittedClassInput =>
        Tendsto (fun t : Real => stationaryPoissonWorkPastAggregate x t / t)
          atTop (nhds (M.admittedRate k.1)))
      hcoordinate.measurable.aemeasurable ?_
    rw [hcoordinate.map_eq]
    exact ae_tendsto_stationaryPoissonWorkPastAggregate_div_atTop
      (M.admittedRate_pos k.1)
  refine ae_of_ae_map (μ := targetTag.Ptag.prod passiveBase.Pbase) (f := Prod.snd)
    (p := fun x : PassiveCategory target -> StationaryAdmittedClassInput =>
      Tendsto (fun t : Real => stationaryPoissonWorkPastAggregate (x k) t / t)
        atTop (nhds (M.admittedRate k.1)))
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  simpa [stationaryAdmittedTargetPassiveTaggedInput,
    targetPassiveTaggedArrivalAtZero, targetTag, passiveBase] using hpassive

/-- The finite passive family has its coordinatewise marked-work source rate
simultaneously almost surely. -/
theorem ae_all_tendsto_stationaryAdmittedPassivePastAggregateWork_div_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∀ k : PassiveCategory target,
        Tendsto
          (fun t : Real => stationaryPoissonWorkPastAggregate (z.2 k) t / t)
          atTop (nhds (M.admittedRate k.1)) := by
  rw [ae_all_iff]
  intro k
  exact M.ae_tendsto_stationaryAdmittedPassivePastAggregateWork_div_atTop target k

/-- A finite sum of convergent real-valued functions converges to the sum of
their limits.  This local form avoids any queue-specific or name-based
shortcut when aggregating the finite class family. -/
private theorem tendsto_finset_sum_real
    {ι : Type*} [Fintype ι] {f : ι -> Real -> Real} {l : ι -> Real}
    (h : ∀ i, Tendsto (f i) atTop (nhds (l i))) :
    Tendsto (fun t : Real => Finset.univ.sum (fun i => f i t))
      atTop (nhds (Finset.univ.sum l)) := by
  classical
  simpa only [Finset.sum_apply] using
    (tendsto_finset_sum (s := Finset.univ) (fun i _ => h i))

/-- The literal aggregate source work in `[-t,0)`, normalized by elapsed
time, has the sum of the direct admitted rates. -/
theorem ae_tendsto_stationaryAdmittedTargetPassivePastAggregateWork_div_atTop
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          stationaryAdmittedTargetPassivePastAggregateWork target z t / t)
        atTop
          (nhds (M.admittedRate target +
            Finset.univ.sum (fun k : PassiveCategory target =>
              M.admittedRate k.1))) := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPalmPastWindowLedgerWork_div_atTop target,
    M.ae_all_tendsto_stationaryAdmittedPassivePastAggregateWork_div_atTop target]
    with z htarget hpassive
  have hsum : Tendsto
      (fun t : Real => Finset.univ.sum (fun k : PassiveCategory target =>
        stationaryPoissonWorkPastAggregate (z.2 k) t / t))
      atTop
        (nhds (Finset.univ.sum (fun k : PassiveCategory target =>
          M.admittedRate k.1))) :=
    tendsto_finset_sum_real hpassive
  have htarget' : Tendsto
      (fun t : Real =>
        stationaryAdmittedTargetPalmPastWindowLedgerWork target z t / t)
      atTop (nhds (M.admittedRate target)) := htarget
  have hadd := htarget'.add hsum
  have hfun :
      (fun t : Real =>
        stationaryAdmittedTargetPassivePastAggregateWork target z t / t) =
      fun t : Real =>
        stationaryAdmittedTargetPalmPastWindowLedgerWork target z t / t +
          Finset.univ.sum (fun k : PassiveCategory target =>
            stationaryPoissonWorkPastAggregate (z.2 k) t / t) := by
    funext t
    rw [stationaryAdmittedTargetPassivePastAggregateWork, add_div, Finset.sum_div]
  rw [hfun]
  exact hadd

/-- Splitting a finite class sum at the chosen target identifies the direct
target-plus-passive rate with the source's total admitted rate. -/
theorem stationaryAdmittedTargetPassive_rateSum_eq_totalAdmittedRate
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    M.admittedRate target +
      Finset.univ.sum (fun k : PassiveCategory target => M.admittedRate k.1) =
      Finset.univ.sum M.admittedRate := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne M.admittedRate target]

/-- The literal aggregate source work in `[-t,0)` has normalized rate equal
to the total direct admitted rate across all categories. -/
theorem ae_tendsto_stationaryAdmittedTargetPassivePastAggregateWork_div_atTop_total
    (M : SLA2026BoroughQueueingInput Category) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          stationaryAdmittedTargetPassivePastAggregateWork target z t / t)
        atTop (nhds (Finset.univ.sum M.admittedRate)) := by
  rw [← M.stationaryAdmittedTargetPassive_rateSum_eq_totalAdmittedRate target]
  exact M.ae_tendsto_stationaryAdmittedTargetPassivePastAggregateWork_div_atTop target

/-- Under the paper's per-class GPS slack assumptions, the literal aggregate
source net work in `[-t,0)` has strictly negative normalized drift relative
to the Borough capacity. -/
theorem ae_tendsto_stationaryAdmittedTargetPassivePastAggregateNetWork_div_atTop
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          (stationaryAdmittedTargetPassivePastAggregateWork target z t -
            G.capacity * t) / t)
        atTop (nhds (Finset.univ.sum M.admittedRate - G.capacity)) := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPassivePastAggregateWork_div_atTop_total target]
    with z hwork
  have hcapacity : Tendsto (fun _t : Real => G.capacity) atTop (nhds G.capacity) :=
    tendsto_const_nhds
  refine (hwork.sub hcapacity).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  field_simp [ht_ne]

/-- The aggregate source net-work limiting rate is strictly negative, as a
derived consequence of the source's classwise GPS slack. -/
theorem stationaryAdmittedTargetPassive_totalAdmittedRate_sub_capacity_neg
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
    Finset.univ.sum M.admittedRate - G.capacity < 0 := by
  linarith [G.total_admittedRate_lt_capacity target]

/-- A real-valued process whose normalization by elapsed time converges to a
strictly negative constant itself tends to `-∞`.  This elementary analytic
step is kept local so the source net-work conclusion below does not depend on
any queue recursion or a particular event enumeration. -/
private theorem tendsto_atBot_of_tendsto_div_atTop_of_limit_neg
    {f : Real -> Real} {limit : Real}
    (hlimit : Tendsto (fun t : Real => f t / t) atTop (nhds limit))
    (hneg : limit < 0) :
    Tendsto f atTop atBot := by
  have hhalf_neg : limit / 2 < 0 := by linarith
  have hlinear : Tendsto (fun t : Real => (limit / 2) * t) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg hhalf_neg tendsto_id
  refine Filter.tendsto_atBot.2 ?_
  intro bound
  filter_upwards [
    hlimit.eventually (eventually_lt_nhds (by linarith : limit < limit / 2)),
    eventually_gt_atTop (0 : Real),
    Filter.tendsto_atBot.1 hlinear bound] with t hratio ht_pos hlinear_bound
  have hmul : f t < (limit / 2) * t :=
    (div_lt_iff₀ ht_pos).mp hratio
  exact hmul.le.trans hlinear_bound

/-- Under the source-derived strict aggregate slack, the literal direct
admitted source net work over the half-open physical-time window `[-t,0)`
tends to `-∞` almost surely.  This is a source-input fact only: it neither
selects an event cutoff nor makes a GPS reset, stationary, response, or tail
claim. -/
theorem ae_tendsto_stationaryAdmittedTargetPassivePastAggregateNetWork_atBot
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      Tendsto
        (fun t : Real =>
          stationaryAdmittedTargetPassivePastAggregateWork target z t -
            G.capacity * t)
        atTop atBot := by
  filter_upwards [
    M.ae_tendsto_stationaryAdmittedTargetPassivePastAggregateNetWork_div_atTop
      G target] with z hnet
  exact tendsto_atBot_of_tendsto_div_atTop_of_limit_neg hnet
    (M.stationaryAdmittedTargetPassive_totalAdmittedRate_sub_capacity_neg G target)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements

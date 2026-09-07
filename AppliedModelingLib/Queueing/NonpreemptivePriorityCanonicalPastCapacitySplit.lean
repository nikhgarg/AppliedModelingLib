import AppliedModelingLib.Queueing.MM1DirectCausalWorkloadTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityCapacitySplit
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastReplay

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace MM1DirectCausal

def canonicalPastClassNegativeTimeHistory
    {n : ℕ} (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (i : Fin n) : NegativeTimeHistory :=
  ((past i).2, (past i).1)

theorem measurable_canonicalPastClassNegativeTimeHistory
    {n : ℕ} (i : Fin n) :
    Measurable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      canonicalPastClassNegativeTimeHistory past i) := by
  exact
    ((measurable_snd.comp (measurable_pi_apply i)).prodMk
      (measurable_fst.comp (measurable_pi_apply i)))

theorem map_canonicalPastClassNegativeTimeHistory
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) (i : Fin n) :
    Measure.map (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      canonicalPastClassNegativeTimeHistory past i)
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) =
      negativeTimeHistoryMeasure (arrivalRate i) := by
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (exponentialInterarrivalMeasure (arrivalRate j)).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (arrivalRate i)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (harrivalRate i)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    dsimp [ν]
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (arrivalRate j)) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure (harrivalRate j)
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
    infer_instance
  let historyMap : StationaryPoissonWorkPastCanonicalSample → NegativeTimeHistory :=
    Prod.swap
  have hhistoryMap : Measurable historyMap := measurable_swap
  calc
    Measure.map (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      canonicalPastClassNegativeTimeHistory past i) (Measure.pi ν) =
        Measure.map historyMap (Measure.map (Function.eval i) (Measure.pi ν)) := by
          change Measure.map (historyMap ∘ Function.eval i) (Measure.pi ν) = _
          rw [← Measure.map_map hhistoryMap (measurePreserving_eval ν i).measurable]
    _ = Measure.map historyMap (ν i) := by
          rw [(measurePreserving_eval ν i).map_eq]
    _ = negativeTimeHistoryMeasure (arrivalRate i) := by
          change Measure.map Prod.swap
            ((exponentialInterarrivalMeasure (arrivalRate i)).prod
              (exponentialInterarrivalMeasure (1 : ℝ))) = _
          rw [Measure.prod_swap]
          rfl

theorem integrable_negativeTimeCausalWorkload_canonicalPastClass
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (i : Fin n) :
    Integrable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i))
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (exponentialInterarrivalMeasure (arrivalRate j)).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  let history : (Fin n → StationaryPoissonWorkPastCanonicalSample) → NegativeTimeHistory :=
    fun past => canonicalPastClassNegativeTimeHistory past i
  let workload : NegativeTimeHistory → ℝ :=
    negativeTimeCausalWorkload (capacity i / meanService i)
  have hservice : arrivalRate i < capacity i / meanService i := by
    apply (lt_div_iff₀ (hmeanService i)).2
    simpa [mul_comm] using hclassStable i
  have hhistory : Measure.map history (Measure.pi ν) =
      negativeTimeHistoryMeasure (arrivalRate i) := by
    simpa [history, ν] using
      map_canonicalPastClassNegativeTimeHistory arrivalRate harrivalRate i
  have hworkloadMeas : Measurable workload := by
    exact measurable_negativeTimeCausalWorkload _
  have hmap : Measure.map (workload ∘ history) (Measure.pi ν) =
      mm1PreArrivalWorkloadLaw (arrivalRate i) (capacity i / meanService i) := by
    rw [← Measure.map_map hworkloadMeas
      (measurable_canonicalPastClassNegativeTimeHistory i), hhistory,
      map_negativeTimeCausalWorkload_eq_mm1PreArrivalWorkloadLaw
        (harrivalRate i) hservice]
  have hid : Integrable (fun w : ℝ => w)
      (Measure.map (workload ∘ history) (Measure.pi ν)) := by
    rw [hmap]
    exact integrable_id_mm1PreArrivalWorkloadLaw hservice
  have hmeas : AEMeasurable (workload ∘ history) (Measure.pi ν) :=
    (hworkloadMeas.comp (measurable_canonicalPastClassNegativeTimeHistory i)).aemeasurable
  simpa [workload, history, Function.comp_apply] using
    (integrable_map_measure measurable_id.aestronglyMeasurable hmeas).mp hid

/-- The square of each stable canonical one-class comparator workload is
integrable under the joint canonical past input. -/
theorem integrable_sq_negativeTimeCausalWorkload_canonicalPastClass
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (i : Fin n) :
    Integrable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      (negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)) ^ 2)
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (exponentialInterarrivalMeasure (arrivalRate j)).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  let history : (Fin n → StationaryPoissonWorkPastCanonicalSample) → NegativeTimeHistory :=
    fun past => canonicalPastClassNegativeTimeHistory past i
  let workload : NegativeTimeHistory → ℝ :=
    negativeTimeCausalWorkload (capacity i / meanService i)
  have hservice : arrivalRate i < capacity i / meanService i := by
    apply (lt_div_iff₀ (hmeanService i)).2
    simpa [mul_comm] using hclassStable i
  have hhistory : Measure.map history (Measure.pi ν) =
      negativeTimeHistoryMeasure (arrivalRate i) := by
    simpa [history, ν] using
      map_canonicalPastClassNegativeTimeHistory arrivalRate harrivalRate i
  have hworkloadMeas : Measurable workload := by
    exact measurable_negativeTimeCausalWorkload _
  have hmap : Measure.map (workload ∘ history) (Measure.pi ν) =
      mm1PreArrivalWorkloadLaw (arrivalRate i) (capacity i / meanService i) := by
    rw [← Measure.map_map hworkloadMeas
      (measurable_canonicalPastClassNegativeTimeHistory i), hhistory,
      map_negativeTimeCausalWorkload_eq_mm1PreArrivalWorkloadLaw
        (harrivalRate i) hservice]
  have hsquare : Integrable (fun w : ℝ => w ^ 2)
      (Measure.map (workload ∘ history) (Measure.pi ν)) := by
    rw [hmap]
    exact integrable_sq_mm1PreArrivalWorkloadLaw hservice
  have hmeas : AEMeasurable (workload ∘ history) (Measure.pi ν) :=
    (hworkloadMeas.comp (measurable_canonicalPastClassNegativeTimeHistory i)).aemeasurable
  simpa [workload, history, Function.comp_apply] using
    (integrable_map_measure (measurable_id.aestronglyMeasurable.pow 2) hmeas).mp hsquare

/-- At a stable one-class rate pair, every finite reverse replay of a
canonical past coordinate is bounded almost surely by its causal workload. -/
theorem ae_canonicalPastClass_timeReplay_le_negativeTimeCausalWorkload
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (i : Fin n) :
    ∀ᵐ past ∂(Measure.pi fun j =>
      (exponentialInterarrivalMeasure (arrivalRate j)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ N : ℕ,
        timeReplay (capacity i / meanService i) 0
          (canonicalPastClassNegativeTimeHistory past i) N ≤
          negativeTimeCausalWorkload (capacity i / meanService i)
            (canonicalPastClassNegativeTimeHistory past i) := by
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (exponentialInterarrivalMeasure (arrivalRate j)).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  change ∀ᵐ past ∂Measure.pi ν, ∀ N : ℕ,
    timeReplay (capacity i / meanService i) 0
      (canonicalPastClassNegativeTimeHistory past i) N ≤
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)
  have hservice : arrivalRate i < capacity i / meanService i := by
    apply (lt_div_iff₀ (hmeanService i)).2
    simpa [mul_comm] using hclassStable i
  refine MeasureTheory.ae_of_ae_map (μ := Measure.pi ν)
    (f := fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      canonicalPastClassNegativeTimeHistory past i)
    (p := fun h : NegativeTimeHistory => ∀ N : ℕ,
      timeReplay (capacity i / meanService i) 0 h N ≤
        negativeTimeCausalWorkload (capacity i / meanService i) h)
    (measurable_canonicalPastClassNegativeTimeHistory i).aemeasurable ?_
  change ∀ᵐ h ∂Measure.map (fun past : Fin n →
      StationaryPoissonWorkPastCanonicalSample =>
      canonicalPastClassNegativeTimeHistory past i) (Measure.pi ν),
      ∀ N : ℕ,
        timeReplay (capacity i / meanService i) 0 h N ≤
          negativeTimeCausalWorkload (capacity i / meanService i) h
  rw [map_canonicalPastClassNegativeTimeHistory arrivalRate harrivalRate i]
  rw [ae_all_iff]
  intro N
  exact ae_timeReplay_zero_le_negativeTimeCausalWorkload_of_rate_lt
    (harrivalRate i) hservice N

/-- Every class's canonical renewal epochs are nonnegative almost surely
under the finite independent product input. -/
theorem ae_canonicalPastArrivalTime_nonnegative
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) :
    ∀ᵐ past ∂(Measure.pi fun j =>
      (exponentialInterarrivalMeasure (arrivalRate j)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ i : Fin n, ∀ k : ℕ,
        0 ≤ Probability.PoissonProcess.arrivalTime k (past i).1 := by
  let ν : Fin n → Measure StationaryPoissonWorkPastCanonicalSample := fun j =>
    (exponentialInterarrivalMeasure (arrivalRate j)).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  change ∀ᵐ past ∂Measure.pi ν, ∀ i : Fin n, ∀ k : ℕ,
    0 ≤ Probability.PoissonProcess.arrivalTime k (past i).1
  letI (j : Fin n) : IsProbabilityMeasure
      (exponentialInterarrivalMeasure (arrivalRate j)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (harrivalRate j)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by
    dsimp [ν]
    infer_instance
  rw [ae_all_iff]
  intro i
  have hcoordinate : MeasurePreserving (fun past :
      Fin n → StationaryPoissonWorkPastCanonicalSample => (past i).1)
      (Measure.pi ν)
      (exponentialInterarrivalMeasure (arrivalRate i)) := by
    exact (MeasureTheory.measurePreserving_fst : MeasurePreserving Prod.fst
      (ν i) (exponentialInterarrivalMeasure (arrivalRate i))).comp
        (MeasureTheory.measurePreserving_eval ν i)
  refine MeasureTheory.ae_of_ae_map (μ := Measure.pi ν)
    (f := fun past : Fin n → StationaryPoissonWorkPastCanonicalSample => (past i).1)
    (p := fun gaps : ℕ → ℝ => ∀ k : ℕ,
      0 ≤ Probability.PoissonProcess.arrivalTime k gaps)
    hcoordinate.measurable.aemeasurable ?_
  rw [hcoordinate.map_eq]
  exact Probability.PoissonProcess.ae_all_arrivalTime_nonnegative (harrivalRate i)

/-- Restricting the chronological canonical ledger to one class produces the
same finite renewal prefix, read from its oldest arrival to its newest. -/
theorem filter_canonicalNonpreemptivePriorityPastWindowIndices_eq_reverseRange
    {n : ℕ} (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) (selected : Fin n)
    (hstrict : StrictMono (fun k : ℕ =>
      Probability.PoissonProcess.arrivalTime k (past selected).1)) :
    (canonicalNonpreemptivePriorityPastWindowIndices past horizon).filter
        (fun q => q.1 = selected) =
      ((List.range (Probability.PoissonProcess.canonicalRenewalCount horizon
        (past selected).1)).reverse.map (fun k =>
          (Sigma.mk selected k : NonpreemptivePriorityCanonicalPastIndex n))) := by
  classical
  let count := Probability.PoissonProcess.canonicalRenewalCount horizon
    (past selected).1
  let left := (canonicalNonpreemptivePriorityPastWindowIndices past horizon).filter
    (fun q => q.1 = selected)
  let right := (List.range count).reverse.map (fun k =>
    (Sigma.mk selected k : NonpreemptivePriorityCanonicalPastIndex n))
  letI : IsTrans (NonpreemptivePriorityCanonicalPastIndex n)
      (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ _ => nonpreemptivePriorityCanonicalPastIndexLE_trans past⟩
  letI : Std.Antisymm (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨fun _ _ => nonpreemptivePriorityCanonicalPastIndexLE_antisymm past⟩
  letI : Std.Total (nonpreemptivePriorityCanonicalPastIndexLE past) :=
    ⟨nonpreemptivePriorityCanonicalPastIndexLE_total past⟩
  have hleft : left.Pairwise (nonpreemptivePriorityCanonicalPastIndexLE past) := by
    exact (pairwise_nonpreemptivePriorityCanonicalPastIndexLE_windowIndices past horizon).filter _
  have hdescending : (List.range count).reverse.Pairwise (fun first second => second < first) := by
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range
  have hright : right.Pairwise (nonpreemptivePriorityCanonicalPastIndexLE past) := by
    change ((List.range count).reverse.map (fun k =>
      (Sigma.mk selected k : NonpreemptivePriorityCanonicalPastIndex n))).Pairwise _
    rw [List.pairwise_map]
    apply hdescending.imp
    intro first second hsecond_lt_first
    have htime :
        -Probability.PoissonProcess.arrivalTime first (past selected).1 <
          -Probability.PoissonProcess.arrivalTime second (past selected).1 := by
      exact neg_lt_neg (hstrict hsecond_lt_first)
    change nonpreemptivePriorityCanonicalPastIndexKey past (Sigma.mk selected first) ≤
      nonpreemptivePriorityCanonicalPastIndexKey past (Sigma.mk selected second)
    apply Prod.Lex.toLex_le_toLex.mpr
    left
    simpa [nonpreemptivePriorityCanonicalPastIndexKey,
      nonpreemptivePriorityCanonicalPastArrivalTime] using htime
  have hleftNodup : left.Nodup := by
    dsimp only [left]
    unfold canonicalNonpreemptivePriorityPastWindowIndices
    letI : DecidableRel (nonpreemptivePriorityCanonicalPastIndexLE past) := Classical.decRel _
    exact (Finset.sort_nodup _ _).filter
      (fun q : NonpreemptivePriorityCanonicalPastIndex n => q.1 = selected)
  have hrightNodup : right.Nodup := by
    dsimp only [right]
    have hinj : Function.Injective (fun k : ℕ =>
        (Sigma.mk selected k : NonpreemptivePriorityCanonicalPastIndex n)) := by
      intro first second h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [List.nodup_map_iff hinj]
    exact List.nodup_reverse.mpr List.nodup_range
  apply List.Perm.eq_of_pairwise' hleft hright
  apply List.perm_of_nodup_nodup_toFinset_eq hleftNodup hrightNodup
  apply List.toFinset.ext
  intro q
  rcases q with ⟨classIndex, renewalIndex⟩
  simp only [left, right, List.mem_filter, List.mem_reverse, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨hmem, hclass⟩
    have hclass' : classIndex = selected := of_decide_eq_true hclass
    subst classIndex
    have hindex : renewalIndex < count := by
      simpa [count] using
        (mem_canonicalNonpreemptivePriorityPastWindowIndices_iff past horizon
          (Sigma.mk selected renewalIndex)).mp hmem
    exact ⟨renewalIndex, hindex, rfl⟩
  · rintro ⟨index, hindex, heq⟩
    have hclass : classIndex = selected := by
      simpa only [Sigma.mk.inj_iff] using (congrArg Sigma.fst heq).symm
    subst classIndex
    have hindices : index = renewalIndex := by
      simpa only [Sigma.mk.inj_iff] using congrArg Sigma.snd heq
    subst index
    exact ⟨(mem_canonicalNonpreemptivePriorityPastWindowIndices_iff past horizon
      (Sigma.mk selected renewalIndex)).mpr (by simpa [count] using hindex), by simp⟩

/-- Every job in a canonical finite strict-past window occurs no earlier than
the window's left endpoint. -/
theorem canonicalNonpreemptivePriorityPastWindowArrivalTime_lower_bound
    {n : ℕ} (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) (q : NonpreemptivePriorityCanonicalPastIndex n)
    (hmem : q ∈ canonicalNonpreemptivePriorityPastWindowIndices past horizon) :
    -horizon ≤ nonpreemptivePriorityCanonicalPastArrivalTime past q := by
  have hindex : q.2 < Probability.PoissonProcess.canonicalRenewalCount horizon (past q.1).1 :=
    (mem_canonicalNonpreemptivePriorityPastWindowIndices_iff past horizon q).mp hmem
  have hcountpos : 0 < Probability.PoissonProcess.canonicalRenewalCount horizon
      (past q.1).1 := lt_of_le_of_lt (Nat.zero_le _) hindex
  have hfuture : ∃ k : ℕ,
      horizon < Probability.PoissonProcess.arrivalTime k (past q.1).1 := by
    by_contra hnot
    have hzero : Probability.PoissonProcess.canonicalRenewalCount horizon (past q.1).1 = 0 := by
      simp [Probability.PoissonProcess.canonicalRenewalCount, hnot]
    omega
  have htime : Probability.PoissonProcess.arrivalTime q.2 (past q.1).1 ≤ horizon :=
    Probability.PoissonProcess.arrivalTime_le_of_lt_canonicalRenewalCount
      horizon (past q.1).1 hfuture hindex
  exact neg_le_neg htime

/-- The canonical chronological job list is ordered by nondecreasing physical
arrival time. -/
theorem pairwise_canonicalNonpreemptivePriorityPastWindowJobs_arrivalTime
    {n : ℕ} (meanService : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) :
    (canonicalNonpreemptivePriorityPastWindowJobs meanService past horizon).Pairwise
      (fun first second => first.arrivalTime ≤ second.arrivalTime) := by
  rw [canonicalNonpreemptivePriorityPastWindowJobs, List.pairwise_map]
  apply (pairwise_nonpreemptivePriorityCanonicalPastIndexLE_windowIndices past horizon).imp
  intro first second hle
  change nonpreemptivePriorityCanonicalPastIndexKey past first ≤
    nonpreemptivePriorityCanonicalPastIndexKey past second at hle
  unfold nonpreemptivePriorityCanonicalPastIndexKey at hle
  rw [Prod.Lex.toLex_le_toLex] at hle
  exact hle.elim le_of_lt (fun heq => le_of_eq heq.1)

/-- After selecting one class, scaling its service work, and relabelling its
finite jobs by chronological position, the canonical prefix is the literal
reverse remote-past trace for that class. -/
theorem canonicalPastClassScaledJobs_mapIdentifier_eq_reverseRemotePast
    {n : ℕ} (meanService capacity : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (selected : Fin n) (N : ℕ) :
    (((List.range N).reverse.map (fun k =>
      nonpreemptivePriorityCanonicalPastJob meanService past (Sigma.mk selected k))).map
        (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
          (capacity selected)⁻¹)).map
        (nonpreemptivePriorityJobMapIdentifier (fun q => N - (q.2 + 1))) =
      reverseRemotePastArrivalTraceJobs selected
        (fun k => (capacity selected)⁻¹ * (meanService selected * (past selected).2 k))
        (past selected).1 N := by
  rw [reverseRemotePastArrivalTraceJobs_eq_reverseRange]
  simp only [List.map_map]
  apply List.map_congr_left
  intro k _
  simp [nonpreemptivePriorityCanonicalPastJob,
    nonpreemptivePriorityCanonicalPastServiceWork,
    nonpreemptivePriorityCanonicalPastArrivalTime,
    nonpreemptivePriorityJobClassMaskScaleServiceWork,
    nonpreemptivePriorityJobMapIdentifier,
    Probability.PoissonProcess.arrivalTime,
    Probability.PoissonProcess.interarrival,
    Probability.Queueing.remotePastCumulativeNetInput]

/-- The scaled one-class canonical prefix has the exact finite M/M/1 replay
workload when started at its oldest arrival epoch. -/
theorem canonicalPastClassScaledTerminalResidualWork_eq_timeReplay
    {n : ℕ} (meanService capacity : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (selected : Fin n) (N : ℕ)
    (hmeanService : 0 < meanService selected)
    (hcapacity : 0 < capacity selected) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
      (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N) 0
      (((List.range N).reverse.map (fun k =>
        nonpreemptivePriorityCanonicalPastJob meanService past (Sigma.mk selected k))).map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
            (capacity selected)⁻¹)) 0 =
      timeReplay (capacity selected / meanService selected) 0
        (canonicalPastClassNegativeTimeHistory past selected) N := by
  let jobs := ((List.range N).reverse.map (fun k =>
    nonpreemptivePriorityCanonicalPastJob meanService past (Sigma.mk selected k))).map
      (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
        (capacity selected)⁻¹)
  let relabel : NonpreemptivePriorityCanonicalPastIndex n → ℕ :=
    fun q => N - (q.2 + 1)
  let batch : ℕ → ℝ := fun k =>
    (capacity selected)⁻¹ * (meanService selected * (past selected).2 k)
  let serviceRate : ℝ := capacity selected / meanService selected
  have hbatch : batch = fun k => (past selected).2 k / serviceRate := by
    funext k
    dsimp [batch, serviceRate]
    field_simp [ne_of_gt hmeanService, ne_of_gt hcapacity]
  calc
    nonpreemptivePriorityArrivalTraceTerminalResidualWork
        (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N) 0 jobs 0 =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork
        (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N) 0
        (jobs.map (nonpreemptivePriorityJobMapIdentifier relabel)) 0 := by
          symm
          exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_mapIdentifier
            relabel (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N)
            0 0 jobs
    _ = nonpreemptivePriorityArrivalTraceTerminalResidualWork
        (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N) 0
        (reverseRemotePastArrivalTraceJobs selected batch (past selected).1 N) 0 := by
          rw [show jobs.map (nonpreemptivePriorityJobMapIdentifier relabel) =
            reverseRemotePastArrivalTraceJobs selected batch (past selected).1 N by
              exact canonicalPastClassScaledJobs_mapIdentifier_eq_reverseRemotePast
                meanService capacity past selected N]
    _ = lateBatchPreWorkload
        (Probability.Queueing.reverseRemotePastIncrement batch N)
        (Probability.Queueing.reverseRemotePastIncrement (past selected).1 N) N := by
          rw [← lateBatchArrivalTraceTerminalTime_reverseRemotePastIncrement
            (past selected).1 N]
          exact reverseRemotePastArrivalTraceTerminalResidualWork_eq_lateBatchPreWorkload
            selected batch (past selected).1 N
    _ = lateBatchPreWorkload
        (Probability.Queueing.reverseRemotePastIncrement
          (fun k => (past selected).2 k / serviceRate) N)
        (Probability.Queueing.reverseRemotePastIncrement (past selected).1 N) N := by
          rw [hbatch]
    _ = timeReplay serviceRate 0
        (canonicalPastClassNegativeTimeHistory past selected) N := by
          exact lateBatchPreWorkload_reverse_eq_timeReplay serviceRate
            (canonicalPastClassNegativeTimeHistory past selected) N

/-- Starting a finite canonical one-class prefix at the window boundary has
the same scaled terminal workload as its finite M/M/1 replay. -/
theorem canonicalPastClassWindowScaledTerminalResidualWork_eq_timeReplay
    {n : ℕ} (meanService capacity : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ) (selected : Fin n)
    (hhorizon : 0 ≤ horizon)
    (hstrict : StrictMono (fun k : ℕ =>
      Probability.PoissonProcess.arrivalTime k (past selected).1))
    (hmeanService : 0 < meanService selected)
    (hcapacity : 0 < capacity selected) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
      (((canonicalNonpreemptivePriorityPastWindowIndices past horizon).filter
        (fun q => q.1 = selected)).map
          (nonpreemptivePriorityCanonicalPastJob meanService past) |>.map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork selected
            (capacity selected)⁻¹)) 0 =
      timeReplay (capacity selected / meanService selected) 0
        (canonicalPastClassNegativeTimeHistory past selected)
        (Probability.PoissonProcess.canonicalRenewalCount horizon (past selected).1) := by
  let N := Probability.PoissonProcess.canonicalRenewalCount horizon (past selected).1
  let jobs : List (NonpreemptivePriorityJob n (NonpreemptivePriorityCanonicalPastIndex n)) :=
    (List.range N).reverse.map
      (nonpreemptivePriorityJobClassMaskScaleServiceWork selected (capacity selected)⁻¹ ∘
        nonpreemptivePriorityCanonicalPastJob meanService past ∘
        fun k => (Sigma.mk selected k : NonpreemptivePriorityCanonicalPastIndex n))
  let relabel : NonpreemptivePriorityCanonicalPastIndex n → ℕ :=
    fun q => N - (q.2 + 1)
  let batch : ℕ → ℝ := fun k =>
    (capacity selected)⁻¹ * (meanService selected * (past selected).2 k)
  rw [filter_canonicalNonpreemptivePriorityPastWindowIndices_eq_reverseRange
    past horizon selected hstrict]
  simp only [List.map_map]
  change nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0 jobs 0 = _
  by_cases hN : N = 0
  · subst N
    simp only [hN, jobs, List.range_zero, List.reverse_nil, List.map_nil,
      timeReplay, Probability.Queueing.remotePastReplayFrom,
      Probability.Queueing.lindleyWorkloadFrom]
    change max 0 (0 - (0 - -horizon)) = 0
    rw [max_eq_left (by linarith)]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hfuture : ∃ k : ℕ,
        horizon < Probability.PoissonProcess.arrivalTime k (past selected).1 := by
      by_contra hnot
      have hzero : N = 0 := by
        simp [N, Probability.PoissonProcess.canonicalRenewalCount, hnot]
      exact hN hzero
    rcases Nat.exists_eq_succ_of_ne_zero hN with ⟨M, hNM⟩
    have hMmem : M < Probability.PoissonProcess.canonicalRenewalCount horizon
        (past selected).1 := by
      have : M < N := by
        rw [hNM]
        exact Nat.lt_succ_self M
      simpa [N] using this
    have htime : Probability.PoissonProcess.arrivalTime M (past selected).1 ≤ horizon :=
      Probability.PoissonProcess.arrivalTime_le_of_lt_canonicalRenewalCount
        horizon (past selected).1 hfuture hMmem
    have hcum : Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N =
        Probability.PoissonProcess.arrivalTime M (past selected).1 := by
      rw [hNM]
      simp [Probability.Queueing.remotePastCumulativeNetInput,
        Probability.PoissonProcess.arrivalTime,
        Probability.PoissonProcess.interarrival]
    have hstart : -horizon ≤
        -Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N := by
      rw [hcum]
      exact neg_le_neg htime
    calc
      nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0 jobs 0 =
        nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
          (jobs.map (nonpreemptivePriorityJobMapIdentifier relabel)) 0 := by
            symm
            exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_mapIdentifier
              relabel (-horizon) 0 0 jobs
      _ = nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0
          (reverseRemotePastArrivalTraceJobs selected batch (past selected).1 N) 0 := by
            rw [show jobs.map (nonpreemptivePriorityJobMapIdentifier relabel) =
              reverseRemotePastArrivalTraceJobs selected batch (past selected).1 N by
                simpa [jobs, relabel, batch, List.map_map] using
                  canonicalPastClassScaledJobs_mapIdentifier_eq_reverseRemotePast
                    meanService capacity past selected N]
      _ = nonpreemptivePriorityArrivalTraceTerminalResidualWork
          (-lateBatchArrivalTraceTerminalTime
            (Probability.Queueing.reverseRemotePastIncrement (past selected).1 N) N) 0
          (reverseRemotePastArrivalTraceJobs selected batch (past selected).1 N) 0 := by
            apply reverseRemotePastArrivalTraceTerminalResidualWork_zero_start_eq_oldest
            · exact hNpos
            · rw [lateBatchArrivalTraceTerminalTime_reverseRemotePastIncrement]
              exact hstart
      _ = nonpreemptivePriorityArrivalTraceTerminalResidualWork
          (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N) 0
          (jobs.map (nonpreemptivePriorityJobMapIdentifier relabel)) 0 := by
            rw [show jobs.map (nonpreemptivePriorityJobMapIdentifier relabel) =
              reverseRemotePastArrivalTraceJobs selected batch (past selected).1 N by
                simpa [jobs, relabel, batch, List.map_map] using
                  canonicalPastClassScaledJobs_mapIdentifier_eq_reverseRemotePast
                    meanService capacity past selected N,
              lateBatchArrivalTraceTerminalTime_reverseRemotePastIncrement]
      _ = nonpreemptivePriorityArrivalTraceTerminalResidualWork
          (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N) 0 jobs 0 :=
            nonpreemptivePriorityArrivalTraceTerminalResidualWork_mapIdentifier
              relabel (-Probability.Queueing.remotePastCumulativeNetInput (past selected).1 N)
              0 0 jobs
      _ = timeReplay (capacity selected / meanService selected) 0
          (canonicalPastClassNegativeTimeHistory past selected) N :=
            by
              simpa [jobs, List.map_map] using
                canonicalPastClassScaledTerminalResidualWork_eq_timeReplay
                  meanService capacity past selected N hmeanService hcapacity

/-- A finite canonical multiclass workload is bounded by the sum of
classwise stable M/M/1 finite replays under any positive capacity split. -/
theorem canonicalNonpreemptivePriorityPastWindowTerminalResidualWork_le_sum_timeReplay
    {n : ℕ} (meanService capacity : Fin n → ℝ)
    (past : Fin n → StationaryPoissonWorkPastCanonicalSample)
    (horizon : ℝ)
    (hhorizon : 0 ≤ horizon)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstrict : ∀ i, StrictMono (fun k : ℕ =>
      Probability.PoissonProcess.arrivalTime k (past i).1))
    (hnonnegative : ∀ i k,
      0 ≤ Probability.PoissonProcess.arrivalTime k (past i).1) :
    canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
      meanService past horizon ≤
      ∑ i, capacity i *
        timeReplay (capacity i / meanService i) 0
          (canonicalPastClassNegativeTimeHistory past i)
          (Probability.PoissonProcess.canonicalRenewalCount horizon (past i).1) := by
  let jobs := canonicalNonpreemptivePriorityPastWindowJobs meanService past horizon
  have hstart : ∀ job ∈ jobs, -horizon ≤ job.arrivalTime := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
    exact canonicalNonpreemptivePriorityPastWindowArrivalTime_lower_bound
      past horizon q hq
  have hsorted : jobs.Pairwise (fun first second => first.arrivalTime ≤ second.arrivalTime) :=
    pairwise_canonicalNonpreemptivePriorityPastWindowJobs_arrivalTime
      meanService past horizon
  have hend : ∀ job ∈ jobs, job.arrivalTime ≤ 0 := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
    change -Probability.PoissonProcess.arrivalTime q.2 (past q.1).1 ≤ 0
    exact neg_nonpos.mpr (hnonnegative q.1 q.2)
  have hbound := nonpreemptivePriorityArrivalTraceTerminalResidualWork_le_sum_capacitySplit
    capacity (-horizon) 0 jobs hcapacitySum
  change nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0 jobs 0 ≤ _ at hbound
  calc
    canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork (-horizon) 0 jobs 0 := rfl
    _ ≤ ∑ i, nonpreemptivePriorityCapacitySplitTerminalResidualWork
        capacity (-horizon) (fun _ => 0) jobs 0 i := hbound
    _ = ∑ i, capacity i * nonpreemptivePriorityArrivalTraceTerminalResidualWork
        (-horizon) 0
        (jobs.map (nonpreemptivePriorityJobClassMaskScaleServiceWork i
          (capacity i)⁻¹)) 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [nonpreemptivePriorityCapacitySplitTerminalResidualWork_apply_eq_classCapacitySplitTerminalResidualWork]
          simpa using
            classCapacitySplitTerminalResidualWork_eq_scale_arrivalTraceTerminalResidualWork
              capacity i (hcapacity i) (-horizon) 0 0 jobs
    _ = ∑ i, capacity i * nonpreemptivePriorityArrivalTraceTerminalResidualWork
        (-horizon) 0
        ((jobs.filter fun job => job.priority = i).map
          (nonpreemptivePriorityJobClassMaskScaleServiceWork i (capacity i)⁻¹)) 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [nonpreemptivePriorityArrivalTraceTerminalResidualWork_map_classMaskScaleServiceWork_eq_filter
            (-horizon) 0 i (capacity i)⁻¹ jobs (by linarith) hstart hsorted hend]
    _ = ∑ i, capacity i *
        timeReplay (capacity i / meanService i) 0
          (canonicalPastClassNegativeTimeHistory past i)
          (Probability.PoissonProcess.canonicalRenewalCount horizon (past i).1) := by
          apply Finset.sum_congr rfl
          intro i _
          have hfilter : (jobs.filter fun job => job.priority = i) =
              ((canonicalNonpreemptivePriorityPastWindowIndices past horizon).filter
                (fun q => q.1 = i)).map
                (nonpreemptivePriorityCanonicalPastJob meanService past) := by
            unfold jobs canonicalNonpreemptivePriorityPastWindowJobs
            rw [List.filter_map]
            rfl
          rw [hfilter]
          exact congrArg (fun x => capacity i * x)
            (canonicalPastClassWindowScaledTerminalResidualWork_eq_timeReplay
              meanService capacity past horizon i hhorizon (hstrict i)
              (hmeanService i) (hcapacity i))

/-- Under classwise stability, every finite canonical multiclass workload is
almost surely bounded by the integrable sum of its causal one-class workload
comparators. -/
theorem ae_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork_le_sum_negativeTimeCausalWorkload
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    ∀ᵐ past ∂(Measure.pi fun j =>
      (exponentialInterarrivalMeasure (arrivalRate j)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))),
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
        meanService past horizon ≤
        ∑ i, capacity i *
          negativeTimeCausalWorkload (capacity i / meanService i)
            (canonicalPastClassNegativeTimeHistory past i) := by
  have hstrict := ae_multiclassCanonicalPastArrivalTime_strictMono
    arrivalRate harrivalRate
  have hnonnegative := ae_canonicalPastArrivalTime_nonnegative
    arrivalRate harrivalRate
  have hreplay : ∀ᵐ past ∂(Measure.pi fun j =>
      (exponentialInterarrivalMeasure (arrivalRate j)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ i : Fin n, ∀ N : ℕ,
        timeReplay (capacity i / meanService i) 0
          (canonicalPastClassNegativeTimeHistory past i) N ≤
          negativeTimeCausalWorkload (capacity i / meanService i)
            (canonicalPastClassNegativeTimeHistory past i) := by
    rw [ae_all_iff]
    intro i
    exact ae_canonicalPastClass_timeReplay_le_negativeTimeCausalWorkload
      arrivalRate meanService capacity harrivalRate hmeanService hclassStable i
  filter_upwards [hstrict, hnonnegative, hreplay]
    with past hstrictPast hnonnegativePast hreplayPast
  calc
    canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon ≤
        ∑ i, capacity i *
          timeReplay (capacity i / meanService i) 0
            (canonicalPastClassNegativeTimeHistory past i)
            (Probability.PoissonProcess.canonicalRenewalCount horizon (past i).1) :=
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork_le_sum_timeReplay
        meanService capacity past horizon hhorizon hcapacitySum hcapacity hmeanService
        hstrictPast hnonnegativePast
    _ ≤ ∑ i, capacity i *
          negativeTimeCausalWorkload (capacity i / meanService i)
            (canonicalPastClassNegativeTimeHistory past i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_left
        (hreplayPast i
          (Probability.PoissonProcess.canonicalRenewalCount horizon (past i).1))
        (hcapacity i).le

/-- The finite capacity-split causal comparator has a finite first moment
under the independent canonical past input. -/
theorem integrable_canonicalPastCapacitySplitCausalBound
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i) :
    Integrable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      ∑ i, capacity i *
        negativeTimeCausalWorkload (capacity i / meanService i)
          (canonicalPastClassNegativeTimeHistory past i))
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro i _
  exact (integrable_negativeTimeCausalWorkload_canonicalPastClass
    arrivalRate meanService capacity harrivalRate hmeanService hclassStable i).const_mul
      (capacity i)

/-- The stable finite capacity-split causal comparison workload has an
integrable square. -/
theorem integrable_sq_canonicalPastCapacitySplitCausalBound
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i) :
    Integrable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      (∑ i, capacity i *
        negativeTimeCausalWorkload (capacity i / meanService i)
          (canonicalPastClassNegativeTimeHistory past i)) ^ 2)
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
  let ν : Measure (Fin n → StationaryPoissonWorkPastCanonicalSample) :=
    Measure.pi fun j =>
      (exponentialInterarrivalMeasure (arrivalRate j)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))
  let workload : Fin n →
      (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun i past =>
    capacity i * negativeTimeCausalWorkload (capacity i / meanService i)
      (canonicalPastClassNegativeTimeHistory past i)
  have hmem : ∀ i : Fin n, MemLp (workload i) 2 ν := by
    intro i
    apply (memLp_two_iff_integrable_sq (by
      exact ((measurable_negativeTimeCausalWorkload _).comp
        (measurable_canonicalPastClassNegativeTimeHistory i)).const_mul _ |>.aestronglyMeasurable)).2
    simpa [workload, mul_pow] using
      (integrable_sq_negativeTimeCausalWorkload_canonicalPastClass
        arrivalRate meanService capacity harrivalRate hmeanService hclassStable i).const_mul
          (capacity i ^ 2)
  simpa only [ν, workload, Finset.sum_apply] using
    (MeasureTheory.memLp_finset_sum Finset.univ fun i _ => hmem i).integrable_sq

/-- Every finite canonical priority workload is integrable when a positive
classwise stable capacity split is available. -/
theorem integrable_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    Integrable (fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
        meanService past horizon)
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
  let bound : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    ∑ i, capacity i *
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)
  have hbound : Integrable bound
      (Measure.pi fun j =>
        (exponentialInterarrivalMeasure (arrivalRate j)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [bound] using integrable_canonicalPastCapacitySplitCausalBound
      arrivalRate meanService capacity harrivalRate hmeanService hclassStable
  refine Integrable.mono' hbound
    (measurable_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
      meanService horizon).aestronglyMeasurable ?_
  filter_upwards [
    ae_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork_le_sum_negativeTimeCausalWorkload
      arrivalRate meanService capacity harrivalRate hmeanService hclassStable
      hcapacitySum hcapacity horizon hhorizon] with past hle
  have hnonnegative : 0 ≤
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService past horizon := by
    unfold canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
      nonpreemptivePriorityArrivalTraceTerminalResidualWork
    exact le_max_left _ _
  have hboundNonnegative : 0 ≤ bound past := le_trans hnonnegative hle
  simpa [bound, Real.norm_eq_abs, abs_of_nonneg hnonnegative,
    abs_of_nonneg hboundNonnegative] using hle

/-- The causal stationary priority workload is bounded almost surely by the
same classwise causal M/M/1 comparison after the canonical-past input map. -/
theorem ae_stationaryPriorityRemotePastResidualWork_le_canonicalPastCapacitySplitCausalBound
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      stationaryPriorityRemotePastResidualWork meanService omega ≤
        ∑ i, capacity i *
          negativeTimeCausalWorkload (capacity i / meanService i)
            (canonicalPastClassNegativeTimeHistory
              (multiclassStationaryPoissonWorkPastCanonicalInput omega) i) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let bound : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    ∑ i, capacity i *
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)
  have hcanonical : ∀ᵐ past ∂(Measure.pi fun i =>
      (exponentialInterarrivalMeasure (arrivalRate i)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ horizon : ℕ,
        canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
          meanService past (horizon : ℝ) ≤ bound past := by
    rw [ae_all_iff]
    intro horizon
    simpa [bound] using
      ae_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork_le_sum_negativeTimeCausalWorkload
        arrivalRate meanService capacity harrivalRate hmeanService hclassStable
        hcapacitySum hcapacity (horizon : ℝ) (Nat.cast_nonneg horizon)
  have hinput : MeasurePreserving canonical P
      (Measure.pi fun i =>
        (exponentialInterarrivalMeasure (arrivalRate i)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [canonical, P] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonicalStationary : ∀ᵐ omega ∂P,
      ∀ horizon : ℕ,
        canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
          (canonical omega) (horizon : ℝ) ≤ bound (canonical omega) := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := canonical)
      (p := fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
        ∀ horizon : ℕ,
          canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
            meanService past (horizon : ℝ) ≤ bound past)
      hinput.measurable.aemeasurable ?_
    rw [hinput.map_eq]
    exact hcanonical
  have hfinite : ∀ᵐ omega ∂P, ∀ horizon : ℕ,
      stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
        (-(horizon : ℝ)) 0 =
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (canonical omega) (horizon : ℝ) := by
    rw [ae_all_iff]
    intro horizon
    simpa [P, canonical] using
      ae_stationaryPriorityFiniteWindowTerminalResidualWork_eq_canonicalPast
        arrivalRate meanService harrivalRate (horizon : ℝ)
  filter_upwards [hcanonicalStationary, hfinite,
    ae_eventually_stationaryPriorityFiniteWindowTerminalResidualWork_eq_remotePast
      arrivalRate meanService harrivalRate hmeanService htotalStable]
    with omega hcanonicalOmega hfiniteOmega heventual
  rcases Filter.eventually_atTop.1 heventual with ⟨horizon, hhorizon⟩
  calc
    stationaryPriorityRemotePastResidualWork meanService omega =
        stationaryPriorityFiniteWindowTerminalResidualWork meanService omega
          (-(horizon : ℝ)) 0 := (hhorizon horizon le_rfl).symm
    _ = canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (canonical omega) (horizon : ℝ) := hfiniteOmega horizon
    _ ≤ bound (canonical omega) := hcanonicalOmega horizon

/-- The selected-arrival causal workload has the same pointwise
capacity-split domination after its own canonical strict-past input map. -/
theorem ae_stationaryPriorityClassTaggedRemotePastResidualWork_le_canonicalPastCapacitySplitCausalBound
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (selected : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      stationaryPriorityClassTaggedRemotePastResidualWork meanService selected z ≤
        ∑ i, capacity i *
          negativeTimeCausalWorkload (capacity i / meanService i)
            (canonicalPastClassNegativeTimeHistory
              (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) i) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
      (harrivalRate selected))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let canonical := multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected
  let bound : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    ∑ i, capacity i *
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)
  have hcanonical : ∀ᵐ past ∂(Measure.pi fun i =>
      (exponentialInterarrivalMeasure (arrivalRate i)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ horizon : ℕ,
        canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
          meanService past (horizon : ℝ) ≤ bound past := by
    rw [ae_all_iff]
    intro horizon
    simpa [bound] using
      ae_canonicalNonpreemptivePriorityPastWindowTerminalResidualWork_le_sum_negativeTimeCausalWorkload
        arrivalRate meanService capacity harrivalRate hmeanService hclassStable
        hcapacitySum hcapacity (horizon : ℝ) (Nat.cast_nonneg horizon)
  have hinput : MeasurePreserving canonical P
      (Measure.pi fun i =>
        (exponentialInterarrivalMeasure (arrivalRate i)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [canonical, P] using
      (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate selected)
  have hcanonicalSelected : ∀ᵐ z ∂P,
      ∀ horizon : ℕ,
        canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
          (canonical z) (horizon : ℝ) ≤ bound (canonical z) := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := canonical)
      (p := fun past : Fin n → StationaryPoissonWorkPastCanonicalSample =>
        ∀ horizon : ℕ,
          canonicalNonpreemptivePriorityPastWindowTerminalResidualWork
            meanService past (horizon : ℝ) ≤ bound past)
      hinput.measurable.aemeasurable ?_
    rw [hinput.map_eq]
    exact hcanonical
  have hfinite : ∀ᵐ z ∂P, ∀ horizon : ℕ,
      canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
        meanService selected z (-(horizon : ℝ)) 0 =
      canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (canonical z) (horizon : ℝ) := by
    rw [ae_all_iff]
    intro horizon
    simpa [P, canonical] using
      ae_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)
  filter_upwards [hcanonicalSelected, hfinite,
    ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork_eq_remotePast
      arrivalRate meanService harrivalRate hmeanService htotalStable selected]
    with z hcanonicalZ hfiniteZ heventual
  rcases Filter.eventually_atTop.1 heventual with ⟨horizon, hhorizon⟩
  calc
    stationaryPriorityClassTaggedRemotePastResidualWork meanService selected z =
        canonicalStationaryPriorityClassTaggedFiniteWindowTerminalResidualWork
          meanService selected z (-(horizon : ℝ)) 0 := (hhorizon horizon le_rfl).symm
    _ = canonicalNonpreemptivePriorityPastWindowTerminalResidualWork meanService
        (canonical z) (horizon : ℝ) := hfiniteZ horizon
    _ ≤ bound (canonical z) := hcanonicalZ horizon

/-- Virtual initial work for a capacity split at a selected arrival: each
class receives its causal past-work comparator, and the selected work mark is
assigned to its own class. -/
noncomputable def stationaryPriorityClassTaggedCapacitySplitInitialWork
    {n : ℕ} (meanService capacity : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected) :
    Fin n → ℝ :=
  fun j => capacity j *
      negativeTimeCausalWorkload (capacity j / meanService j)
        (canonicalPastClassNegativeTimeHistory
          (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) j) +
    if j = selected then stationaryPriorityClassTaggedWorkRequirement meanService selected z else 0

theorem sum_stationaryPriorityClassTaggedCapacitySplitInitialWork
    {n : ℕ} (meanService capacity : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected) :
    ∑ j, stationaryPriorityClassTaggedCapacitySplitInitialWork
      meanService capacity selected z j =
      (∑ j, capacity j *
        negativeTimeCausalWorkload (capacity j / meanService j)
          (canonicalPastClassNegativeTimeHistory
            (multiclassStationaryPoissonWorkClassTaggedPastCanonicalInput selected z) j)) +
        stationaryPriorityClassTaggedWorkRequirement meanService selected z := by
  classical
  unfold stationaryPriorityClassTaggedCapacitySplitInitialWork
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The post-admission total workload is bounded almost surely by the total
virtual capacity-split initial work. -/
theorem ae_stationaryPriorityClassTaggedArrivalTotalWork_le_capacitySplitInitialWorkSum
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (selected : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      stationaryPriorityClassTaggedArrivalTotalWork meanService selected z ≤
        ∑ j, stationaryPriorityClassTaggedCapacitySplitInitialWork
          meanService capacity selected z j := by
  filter_upwards [
    ae_stationaryPriorityClassTaggedRemotePastResidualWork_le_canonicalPastCapacitySplitCausalBound
      arrivalRate meanService capacity harrivalRate hmeanService htotalStable
      hclassStable hcapacitySum hcapacity selected] with z hremote
  rw [sum_stationaryPriorityClassTaggedCapacitySplitInitialWork]
  unfold stationaryPriorityClassTaggedArrivalTotalWork
  linarith

/-- The virtual terminal workload of one class after a finite selected
post-arrival trace. -/
noncomputable def stationaryPriorityClassTaggedCapacitySplitTerminalResidualWork
    {n : ℕ} (meanService capacity : Fin n → ℝ) (selected : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected)
    (horizon : ℝ) (j : Fin n) : ℝ :=
  nonpreemptivePriorityCapacitySplitTerminalResidualWork capacity 0
    (stationaryPriorityClassTaggedCapacitySplitInitialWork
      meanService capacity selected z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService selected z horizon)
    horizon j

/-- At every deterministic nonnegative horizon, literal selected-trace work
is dominated almost surely by the sum of virtual class workloads. -/
theorem ae_totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_le_sum_capacitySplit
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (selected : Fin n) (horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      totalNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedFinitePostArrivalState
          meanService selected z horizon) ≤
        ∑ j, stationaryPriorityClassTaggedCapacitySplitTerminalResidualWork
          meanService capacity selected z horizon j := by
  filter_upwards [
    ae_stationaryPriorityClassTaggedArrivalTotalWork_le_capacitySplitInitialWorkSum
      arrivalRate meanService capacity harrivalRate hmeanService htotalStable
      hclassStable hcapacitySum hcapacity selected,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate selected,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService selected] with z hinitial hgood hpositive
  rw [totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_eq_terminalResidualWork
    meanService selected z horizon hhorizon hgood hpositive]
  simpa [stationaryPriorityClassTaggedCapacitySplitTerminalResidualWork] using
    (nonpreemptivePriorityArrivalTraceTerminalResidualWork_le_sum_capacitySplit_of_le
      capacity 0 (stationaryPriorityClassTaggedArrivalTotalWork meanService selected z)
      horizon
      (stationaryPriorityClassTaggedCapacitySplitInitialWork meanService capacity selected z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService selected z horizon)
      hcapacitySum hinitial)

/-- At a fixed nonnegative horizon, a literal selected response tail can occur
only if at least one virtual capacity-split class trace still has positive
work. -/
theorem ae_stationaryPriorityClassTaggedResponseTime_lt_imp_exists_capacitySplitTerminalResidualWork_pos
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i)
    (selected : Fin n) (horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag,
      horizon < stationaryPriorityClassTaggedResponseTime meanService selected z →
        ∃ j, 0 < stationaryPriorityClassTaggedCapacitySplitTerminalResidualWork
          meanService capacity selected z horizon j := by
  classical
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate selected,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService selected,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService htotalStable selected,
    ae_totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_le_sum_capacitySplit
      arrivalRate meanService capacity harrivalRate hmeanService htotalStable hclassStable
      hcapacitySum hcapacity selected horizon hhorizon] with
      z hgood hpositive hcompletion hterminal htail
  rcases hcompletion with ⟨_, completedAt, _, hresponse, hstabilizes⟩
  rcases Filter.eventually_atTop.1 hstabilizes with ⟨bound, hbound⟩
  let terminalHorizon : ℝ := max horizon bound
  have hhorizonTerminal : horizon ≤ terminalHorizon := le_max_left _ _
  have hfinite : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService selected z terminalHorizon = some completedAt :=
    hbound terminalHorizon (le_max_right _ _)
  have hbefore : horizon < completedAt := by
    calc
      horizon < stationaryPriorityClassTaggedResponseTime meanService selected z := htail
      _ = completedAt := hresponse
  have htotalPositive : 0 < totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalState
        meanService selected z horizon) := by
    exact totalResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState_pos_of_lt_responseTime
      meanService selected z horizon terminalHorizon completedAt hgood hpositive
      hhorizon hhorizonTerminal hbefore hfinite
  have hsumPositive : 0 < ∑ j,
      stationaryPriorityClassTaggedCapacitySplitTerminalResidualWork
        meanService capacity selected z horizon j :=
    lt_of_lt_of_le htotalPositive hterminal
  by_contra hnone
  push Not at hnone
  have hsumNonpositive : ∑ j,
      stationaryPriorityClassTaggedCapacitySplitTerminalResidualWork
        meanService capacity selected z horizon j ≤ 0 := by
    exact Finset.sum_nonpos fun j _ => hnone j
  linarith

/-- The stationary priority workload has a finite first moment whenever it
admits a positive classwise stable capacity split. -/
theorem integrable_stationaryPriorityRemotePastResidualWork_of_classCapacitySplit
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i) :
    Integrable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let canonicalBound : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    ∑ i, capacity i *
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)
  have hinput : MeasurePreserving canonical P
      (Measure.pi fun i =>
        (exponentialInterarrivalMeasure (arrivalRate i)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [canonical, P] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonicalIntegrable : Integrable canonicalBound
      (Measure.pi fun i =>
        (exponentialInterarrivalMeasure (arrivalRate i)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [canonicalBound] using integrable_canonicalPastCapacitySplitCausalBound
      arrivalRate meanService capacity harrivalRate hmeanService hclassStable
  have hboundIntegrable : Integrable (canonicalBound ∘ canonical) P :=
    hinput.integrable_comp_of_integrable hcanonicalIntegrable
  refine Integrable.mono' hboundIntegrable
    (aemeasurable_stationaryPriorityRemotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService htotalStable).aestronglyMeasurable ?_
  filter_upwards [
    ae_stationaryPriorityRemotePastResidualWork_le_canonicalPastCapacitySplitCausalBound
      arrivalRate meanService capacity harrivalRate hmeanService htotalStable
      hclassStable hcapacitySum hcapacity,
    ae_nonnegative_stationaryPriorityRemotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService htotalStable]
    with omega hle hnonnegative
  have hboundNonnegative : 0 ≤ (canonicalBound ∘ canonical) omega :=
    le_trans hnonnegative hle
  simpa [canonicalBound, canonical, Function.comp_apply,
    Real.norm_eq_abs, abs_of_nonneg hnonnegative,
    abs_of_nonneg hboundNonnegative] using hle

/-- Under a positive stable capacity split, the literal stationary priority
workload has an integrable square.  This is the uniform boundary control used
when finite trace energy identities are passed to the remote-past state. -/
theorem integrable_sq_stationaryPriorityRemotePastResidualWork_of_classCapacitySplit
    {n : ℕ} (arrivalRate meanService capacity : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hclassStable : ∀ i, arrivalRate i * meanService i < capacity i)
    (hcapacitySum : ∑ i, capacity i = 1)
    (hcapacity : ∀ i, 0 < capacity i) :
    Integrable (fun omega =>
      (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let canonical := multiclassStationaryPoissonWorkPastCanonicalInput (Class := Fin n)
  let canonicalBound : (Fin n → StationaryPoissonWorkPastCanonicalSample) → ℝ := fun past =>
    ∑ i, capacity i *
      negativeTimeCausalWorkload (capacity i / meanService i)
        (canonicalPastClassNegativeTimeHistory past i)
  have hinput : MeasurePreserving canonical P
      (Measure.pi fun i =>
        (exponentialInterarrivalMeasure (arrivalRate i)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [canonical, P] using
      (multiclassStationaryPoissonWorkPastCanonicalInput_measurePreserving
        (Class := Fin n) arrivalRate harrivalRate)
  have hcanonicalIntegrable : Integrable (fun past => (canonicalBound past) ^ 2)
      (Measure.pi fun i =>
        (exponentialInterarrivalMeasure (arrivalRate i)).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [canonicalBound] using integrable_sq_canonicalPastCapacitySplitCausalBound
      arrivalRate meanService capacity harrivalRate hmeanService hclassStable
  have hboundIntegrable : Integrable (fun omega =>
      (canonicalBound (canonical omega)) ^ 2) P :=
    hinput.integrable_comp_of_integrable hcanonicalIntegrable
  refine Integrable.mono' hboundIntegrable
    ((aemeasurable_stationaryPriorityRemotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService htotalStable).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [
    ae_stationaryPriorityRemotePastResidualWork_le_canonicalPastCapacitySplitCausalBound
      arrivalRate meanService capacity harrivalRate hmeanService htotalStable
      hclassStable hcapacitySum hcapacity,
    ae_nonnegative_stationaryPriorityRemotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService htotalStable]
    with omega hle hnonnegative
  have hboundNonnegative : 0 ≤ canonicalBound (canonical omega) :=
    le_trans hnonnegative hle
  have hsq : (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2 ≤
      (canonicalBound (canonical omega)) ^ 2 :=
    (sq_le_sq₀ hnonnegative hboundNonnegative).2 hle
  simpa [P, canonicalBound, canonical, Real.norm_eq_abs] using hsq

/-- Strict aggregate stability supplies a positive virtual capacity for every
nonempty finite class set: each class receives its offered load plus an equal
share of aggregate slack. -/
theorem exists_positive_classCapacitySplit_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) :
    ∃ capacity : Fin n → ℝ,
      (∑ i, capacity i = 1) ∧
      (∀ i, 0 < capacity i) ∧
      (∀ i, arrivalRate i * meanService i < capacity i) := by
  let load : Fin n → ℝ := fun i => arrivalRate i * meanService i
  let slack : ℝ := 1 - ∑ i, load i
  let share : ℝ := slack / (n : ℝ)
  have hslack : 0 < slack := by
    dsimp [slack, load]
    linarith
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hshare : 0 < share := div_pos hslack hnReal
  refine ⟨fun i => load i + share, ?_, ?_, ?_⟩
  · calc
      ∑ i, (load i + share) = (∑ i, load i) + ∑ _i : Fin n, share :=
        Finset.sum_add_distrib
      _ = (∑ i, load i) + (n : ℝ) * share := by simp
      _ = 1 := by
        dsimp [share, slack]
        field_simp [ne_of_gt hnReal]
        ring
  · intro i
    exact add_pos_of_nonneg_of_pos
      (mul_pos (harrivalRate i) (hmeanService i)).le hshare
  · intro i
    dsimp [load]
    linarith

/-- The literal stationary workload is integrable under strict total load for
any nonempty finite set of positive-rate, positive-mean classes. -/
theorem integrable_stationaryPriorityRemotePastResidualWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) :
    Integrable (stationaryPriorityRemotePastResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  rcases exists_positive_classCapacitySplit_of_totalStable
    arrivalRate meanService harrivalRate hmeanService htotalStable hn with
    ⟨capacity, hsum, hpositive, hstable⟩
  exact integrable_stationaryPriorityRemotePastResidualWork_of_classCapacitySplit
    arrivalRate meanService capacity harrivalRate hmeanService htotalStable
    hstable hsum hpositive

/-- Under strict aggregate stability, the literal stationary priority workload
has an integrable square. -/
theorem integrable_sq_stationaryPriorityRemotePastResidualWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) :
    Integrable (fun omega =>
      (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  rcases exists_positive_classCapacitySplit_of_totalStable
    arrivalRate meanService harrivalRate hmeanService htotalStable hn with
    ⟨capacity, hsum, hpositive, hstable⟩
  exact integrable_sq_stationaryPriorityRemotePastResidualWork_of_classCapacitySplit
    arrivalRate meanService capacity harrivalRate hmeanService htotalStable
    hstable hsum hpositive

/-- At a selected Palm arrival, the causal pre-arrival workload has a finite
first moment under strict total load. -/
theorem integrable_stationaryPriorityClassTaggedRemotePastResidualWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (selected : Fin n) :
    Integrable (stationaryPriorityClassTaggedRemotePastResidualWork meanService selected)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le selected.1) selected.2
  exact (integrable_stationaryPriorityClassTaggedRemotePastResidualWork_iff_stationary
    arrivalRate meanService harrivalRate hmeanService htotalStable selected).mpr
      (integrable_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService htotalStable hn)

/-- The post-admission total work seen at a selected Palm arrival is
integrable under strict total load. -/
theorem integrable_stationaryPriorityClassTaggedArrivalTotalWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalStable : ∑ i, arrivalRate i * meanService i < 1)
    (selected : Fin n) :
    Integrable (stationaryPriorityClassTaggedArrivalTotalWork meanService selected)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le selected.1) selected.2
  exact (integrable_stationaryPriorityClassTaggedArrivalTotalWork_iff_stationary
    arrivalRate meanService harrivalRate hmeanService htotalStable selected).mpr
      (integrable_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService htotalStable hn)

end MM1DirectCausal

end

end AppliedModelingLib.Queueing

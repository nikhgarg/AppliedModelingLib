import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalPastReward
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors
import Mathlib.Tactic

/-!
# Independent tag and past factors for a marked two-sided renewal input

The direct marked-renewal M/M/1 comparator needs to keep the target job's
own work mark separate from its entire literal negative-time history.  This
module gives that product decomposition on the actual source carrier:
two-sided rate-`rate` arrival gaps together with an independent two-sided
unit-exponential work path.

It is an input-law factorization only.  It does not construct a workload,
identify a stationary queue law, or prove a response-time tail.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The current tag work, its complete negative-index work path, and the
complete negative-index arrival-gap path.  The positive tails and the
arrival path's index-zero coordinate are intentionally discarded: neither is
an input to the pre-tag FCFS replay. -/
def markedRenewalTagWorkPastFactors (z : TwoSidedMarkedRenewalSample) :
    (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) :=
  ((twoSidedGap 0 z.2, fun n => twoSidedGap (Int.negSucc n) z.2),
    fun n => twoSidedGap (Int.negSucc n) z.1)

theorem measurable_markedRenewalTagWorkPastFactors :
    Measurable markedRenewalTagWorkPastFactors := by
  exact
    ((Measurable.prodMk
      ((measurable_twoSidedGap 0).comp measurable_snd)
      (measurable_pi_iff.2 fun n =>
        (measurable_twoSidedGap (Int.negSucc n)).comp measurable_snd)).prodMk
      (measurable_pi_iff.2 fun n =>
        (measurable_twoSidedGap (Int.negSucc n)).comp measurable_fst))

/-- Repackage the three factors retained from one two-sided path: its central
coordinate, its positive tail, and its negative tail. -/
private def headPositiveNegativeToHeadNegative :
    ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) → ℝ × (ℕ → ℝ) :=
  fun x => (x.1.1, x.2)

private theorem measurable_headPositiveNegativeToHeadNegative :
    Measurable headPositiveNegativeToHeadNegative := by
  exact measurable_fst.comp measurable_fst |>.prodMk measurable_snd

/-- The discarded positive tail can be integrated out from the literal
two-sided iid exponential factorization. -/
private theorem map_headPositiveNegativeToHeadNegative
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map headPositiveNegativeToHeadNegative
      (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate)) =
      (expMeasure rate).prod (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  calc
    Measure.map headPositiveNegativeToHeadNegative
        (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          (exponentialInterarrivalMeasure rate)) =
        Measure.map (Prod.map Prod.fst id)
          (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
            (exponentialInterarrivalMeasure rate)) := by
            rfl
    _ = (Measure.map Prod.fst
          ((expMeasure rate).prod (exponentialInterarrivalMeasure rate))).prod
        (Measure.map id (exponentialInterarrivalMeasure rate)) := by
          rw [← Measure.map_prod_map _ _ measurable_fst measurable_id]
    _ = (expMeasure rate).prod (exponentialInterarrivalMeasure rate) := by
          rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.map_id]

/-- The literal current work mark is independent of the complete literal
negative-time arrival/work input.  This equality is on the direct marked
renewal source law; it does not introduce a uniformized event clock. -/
theorem map_markedRenewalTagWorkPastFactors_twoSidedMarkedRenewalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map markedRenewalTagWorkPastFactors
      (twoSidedMarkedRenewalMeasure rate) =
      ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let arrivalFactors : (ℤ → ℝ) → ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
    twoSidedHeadPositiveNegative
  let workFactors : (ℤ → ℝ) → ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
    twoSidedHeadPositiveNegative
  let retain :
      (((ℝ × (ℕ → ℝ)) × (ℕ → ℝ)) ×
        ((ℝ × (ℕ → ℝ)) × (ℕ → ℝ))) →
      (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) :=
    fun x => (headPositiveNegativeToHeadNegative x.2, x.1.2)
  have hretain : Measurable retain := by
    exact measurable_swap.comp
      (measurable_snd.prodMap measurable_headPositiveNegativeToHeadNegative)
  have hfactor :
      Measure.map (Prod.map arrivalFactors workFactors)
        (twoSidedMarkedRenewalMeasure rate) =
        (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          (exponentialInterarrivalMeasure rate)).prod
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by
    change Measure.map (Prod.map arrivalFactors workFactors)
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) = _
    rw [← Measure.map_prod_map _ _
      measurable_twoSidedHeadPositiveNegative measurable_twoSidedHeadPositiveNegative,
      map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure hrate,
      map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure (by norm_num)]
  calc
    Measure.map markedRenewalTagWorkPastFactors
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map retain
          (Measure.map (Prod.map arrivalFactors workFactors)
            (twoSidedMarkedRenewalMeasure rate)) := by
          symm
          rw [Measure.map_map hretain
            (measurable_twoSidedHeadPositiveNegative.prodMap
              measurable_twoSidedHeadPositiveNegative)]
          rfl
    _ = Measure.map retain
        ((((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
          (exponentialInterarrivalMeasure rate)).prod
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ)))) := by rw [hfactor]
    _ = (Measure.map headPositiveNegativeToHeadNegative
          (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
            (exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (Measure.map Prod.snd
          (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
            (exponentialInterarrivalMeasure rate))) := by
          calc
            Measure.map retain
                ((((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
                  (exponentialInterarrivalMeasure rate)).prod
                (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
                  (exponentialInterarrivalMeasure (1 : ℝ)))) =
                Measure.map Prod.swap
                  (Measure.map
                    (Prod.map Prod.snd headPositiveNegativeToHeadNegative)
                    ((((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
                      (exponentialInterarrivalMeasure rate)).prod
                    (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
                      (exponentialInterarrivalMeasure (1 : ℝ))))) := by
                symm
                rw [Measure.map_map measurable_swap
                  (measurable_snd.prodMap measurable_headPositiveNegativeToHeadNegative)]
                rfl
            _ = Measure.map Prod.swap
                ((Measure.map Prod.snd
                  (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
                    (exponentialInterarrivalMeasure rate))).prod
                  (Measure.map headPositiveNegativeToHeadNegative
                    (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
                      (exponentialInterarrivalMeasure (1 : ℝ))))) := by
                rw [← Measure.map_prod_map _ _ measurable_snd
                  measurable_headPositiveNegativeToHeadNegative]
            _ = _ := by rw [Measure.prod_swap]
    _ = ((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure rate) := by
          rw [map_headPositiveNegativeToHeadNegative (by norm_num),
            Measure.map_snd_prod, measure_univ, one_smul]

/-- The direct source tag's work coordinate has the literal unit-exponential
law.  The stronger preceding factorization retains the whole past input at
the same time, which is what a later workload-plus-tag convolution needs. -/
theorem twoSidedMarkedRenewal_tagWork_hasLaw
    {rate : ℝ} (hrate : 0 < rate) :
    HasLaw (fun z : TwoSidedMarkedRenewalSample => twoSidedGap 0 z.2)
      (expMeasure (1 : ℝ)) (twoSidedMarkedRenewalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  let hfactor :=
    map_markedRenewalTagWorkPastFactors_twoSidedMarkedRenewalMeasure hrate
  let extract : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) → ℝ := fun x => x.1.1
  have hextract : Measurable extract := by
    exact measurable_fst.comp measurable_fst
  have htag_factor :
      (fun z : TwoSidedMarkedRenewalSample => twoSidedGap 0 z.2) =
        extract ∘ markedRenewalTagWorkPastFactors := by
    rfl
  refine ⟨(hextract.comp measurable_markedRenewalTagWorkPastFactors).aemeasurable, ?_⟩
  calc
    Measure.map (fun z : TwoSidedMarkedRenewalSample => twoSidedGap 0 z.2)
        (twoSidedMarkedRenewalMeasure rate) =
        Measure.map extract
          (Measure.map markedRenewalTagWorkPastFactors
            (twoSidedMarkedRenewalMeasure rate)) := by
          rw [htag_factor, ← Measure.map_map hextract
            measurable_markedRenewalTagWorkPastFactors]
    _ = Measure.map extract
        (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure rate)) := by rw [hfactor]
    _ = expMeasure (1 : ℝ) := by
          change Measure.map (fun x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) => x.1.1)
            (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
              (exponentialInterarrivalMeasure rate)) = _
          calc
            Measure.map (fun x : (ℝ × (ℕ → ℝ)) × (ℕ → ℝ) => x.1.1)
                (((expMeasure (1 : ℝ)).prod (exponentialInterarrivalMeasure (1 : ℝ))).prod
                  (exponentialInterarrivalMeasure rate)) =
                Measure.map Prod.fst
                  (Measure.map Prod.fst
                    (((expMeasure (1 : ℝ)).prod
                      (exponentialInterarrivalMeasure (1 : ℝ))).prod
                      (exponentialInterarrivalMeasure rate))) := by
                  symm
                  rw [Measure.map_map measurable_fst measurable_fst]
                  rfl
            _ = _ := by
                  rw [Measure.map_fst_prod, measure_univ, one_smul,
                    Measure.map_fst_prod, measure_univ, one_smul]

end

end AppliedModelingLib.Probability.PoissonProcess

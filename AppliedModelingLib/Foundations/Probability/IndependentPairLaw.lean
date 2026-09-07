import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib

/-!
# Joint law of independent observables

This small transport lemma packages two marginal laws and an independence
proof into the exact product law of the observable pair.  It is useful when a
source construction establishes its marginals and factorization separately.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega Alpha Beta : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Alpha] [MeasurableSpace Beta]
  {P : Measure Omega} {X : Omega -> Alpha} {Y : Omega -> Beta}
  {mu : Measure Alpha} {nu : Measure Beta}

/-- Independent observables with known marginal laws have their product joint
law. -/
theorem indepFun_hasLaw_prodMk
    [IsFiniteMeasure P]
    (hX : HasLaw X mu P) (hY : HasLaw Y nu P)
    (hXY : ProbabilityTheory.IndepFun X Y P) :
    HasLaw (fun omega => (X omega, Y omega)) (mu.prod nu) P where
  aemeasurable := hX.aemeasurable.prodMk hY.aemeasurable
  map_eq := by
    rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable).mp hXY, hX.map_eq, hY.map_eq]

/-- The deterministic uninspected tail left by a regenerative source map. -/
def regenerativeTail {State Summary : Type*}
    (step : State -> Summary × State) : State -> State :=
  fun state => (step state).2

/-- The summary exposed at the `n`th deterministic regenerative tail. -/
def regenerativeSummary {State Summary : Type*}
    (step : State -> Summary × State) (n : Nat) : State -> Summary :=
  fun state => (step ((regenerativeTail step)^[n] state)).1

theorem measurable_regenerativeTail {State Summary : Type*}
    [MeasurableSpace State] [MeasurableSpace Summary]
    (step : State -> Summary × State) (hstep : Measurable step) :
    Measurable (regenerativeTail step) :=
  measurable_snd.comp hstep

theorem measurable_regenerativeSummary {State Summary : Type*}
    [MeasurableSpace State] [MeasurableSpace Summary]
    (step : State -> Summary × State) (hstep : Measurable step) (n : Nat) :
    Measurable (regenerativeSummary step n) :=
  measurable_fst.comp (hstep.comp ((measurable_regenerativeTail step hstep).iterate n))

/-- A product law for one deterministic source step makes its literal tail
measure-preserving.  No independently resampled continuation is introduced. -/
theorem regenerativeTail_measurePreserving
    {State Summary : Type*} [MeasurableSpace State] [MeasurableSpace Summary]
    (P : Measure State) [IsProbabilityMeasure P]
    (B : Measure Summary) [SFinite B]
    (step : State -> Summary × State) (hstep : Measurable step)
    (hstep_law : Measure.map step P = B.prod P) :
    MeasurePreserving (regenerativeTail step) P P := by
  have hB_univ : B Set.univ = 1 := by
    calc
      B Set.univ = B Set.univ * P Set.univ := by simp
      _ = (B.prod P) (Set.univ ×ˢ Set.univ) := by rw [Measure.prod_prod]
      _ = (B.prod P) Set.univ := by rw [Set.univ_prod_univ]
      _ = (Measure.map step P) Set.univ := by rw [hstep_law]
      _ = P Set.univ := by rw [Measure.map_apply hstep MeasurableSet.univ]; simp
      _ = 1 := measure_univ
  refine ⟨measurable_regenerativeTail step hstep, ?_⟩
  calc
    Measure.map (regenerativeTail step) P =
        Measure.map Prod.snd (Measure.map step P) := by
          rw [Measure.map_map measurable_snd hstep]
          rfl
    _ = Measure.map Prod.snd (B.prod P) := by rw [hstep_law]
    _ = P := by rw [Measure.map_snd_prod, hB_univ, one_smul]

/-- Every deterministic iterate of a regenerative source tail has the
original source law. -/
theorem regenerativeTail_iterate_measurePreserving
    {State Summary : Type*} [MeasurableSpace State] [MeasurableSpace Summary]
    (P : Measure State) [IsProbabilityMeasure P]
    (B : Measure Summary) [SFinite B]
    (step : State -> Summary × State) (hstep : Measurable step)
    (hstep_law : Measure.map step P = B.prod P) (n : Nat) :
    MeasurePreserving ((regenerativeTail step)^[n]) P P :=
  (regenerativeTail_measurePreserving P B step hstep hstep_law).iterate n

/-- The summary at any deterministic regenerative tail has the same law as
the one-step summary. -/
theorem regenerativeSummary_map_eq
    {State Summary : Type*} [MeasurableSpace State] [MeasurableSpace Summary]
    (P : Measure State) [IsProbabilityMeasure P]
    (B : Measure Summary) [SFinite B]
    (step : State -> Summary × State) (hstep : Measurable step)
    (hstep_law : Measure.map step P = B.prod P) (n : Nat) :
    Measure.map (regenerativeSummary step n) P = B := by
  let tail := regenerativeTail step
  let htail := regenerativeTail_iterate_measurePreserving P B step hstep hstep_law n
  calc
    Measure.map (regenerativeSummary step n) P =
        Measure.map Prod.fst (Measure.map step (Measure.map (tail^[n]) P)) := by
          rw [Measure.map_map hstep htail.measurable,
            Measure.map_map measurable_fst (hstep.comp htail.measurable)]
          rfl
    _ = Measure.map Prod.fst (Measure.map step P) := by rw [htail.map_eq]
    _ = Measure.map Prod.fst (B.prod P) := by rw [hstep_law]
    _ = B := by simp

/-- A summary exposed at one regenerative tail is independent of every later
summary that depends only on its literal uninspected continuation. -/
theorem regenerativeSummary_indepFun_succ_add
    {State Summary : Type*} [MeasurableSpace State] [MeasurableSpace Summary]
    (P : Measure State) [IsProbabilityMeasure P]
    (B : Measure Summary) [SFinite B]
    (step : State -> Summary × State) (hstep : Measurable step)
    (hstep_law : Measure.map step P = B.prod P) (n k : Nat) :
    ProbabilityTheory.IndepFun (regenerativeSummary step n)
      (regenerativeSummary step (n + 1 + k)) P := by
  let tail := regenerativeTail step
  let iter := tail^[n]
  let pair : State -> Summary × State := fun state => step (iter state)
  let after : State -> State := fun state => (pair state).2
  have htail : Measurable tail := measurable_regenerativeTail step hstep
  have hiter : MeasurePreserving iter P P := by
    simpa [iter] using
      regenerativeTail_iterate_measurePreserving P B step hstep hstep_law n
  have hpair : Measurable pair := hstep.comp hiter.measurable
  have hpair_law : Measure.map pair P = B.prod P := by
    calc
      Measure.map pair P = Measure.map step (Measure.map iter P) := by
        rw [Measure.map_map hstep hiter.measurable]
        rfl
      _ = Measure.map step P := by rw [hiter.map_eq]
      _ = B.prod P := hstep_law
  have hfst_map : Measure.map (fun state => (pair state).1) P = B := by
    calc
      Measure.map (fun state => (pair state).1) P =
          Measure.map Prod.fst (Measure.map pair P) := by
            rw [Measure.map_map measurable_fst hpair]
            rfl
      _ = Measure.map Prod.fst (B.prod P) := by rw [hpair_law]
      _ = B := by simp
  have hsnd_map : Measure.map after P = P := by
    calc
      Measure.map after P = Measure.map Prod.snd (Measure.map pair P) := by
        rw [Measure.map_map measurable_snd hpair]
        rfl
      _ = Measure.map Prod.snd (B.prod P) := by rw [hpair_law]
      _ = P := by
        rw [Measure.map_snd_prod]
        have hB_univ : B Set.univ = 1 := by
          calc
            B Set.univ = B Set.univ * P Set.univ := by simp
            _ = (B.prod P) (Set.univ ×ˢ Set.univ) := by rw [Measure.prod_prod]
            _ = (B.prod P) Set.univ := by rw [Set.univ_prod_univ]
            _ = (Measure.map step P) Set.univ := by rw [hstep_law]
            _ = P Set.univ := by
              rw [Measure.map_apply hstep MeasurableSet.univ]
              simp
            _ = 1 := measure_univ
        rw [hB_univ, one_smul]
  have hpair_indep : ProbabilityTheory.IndepFun
      (fun state => (pair state).1) after P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((measurable_fst.comp hpair).aemeasurable)
      ((measurable_snd.comp hpair).aemeasurable)).mpr
    change Measure.map pair P =
      (Measure.map (fun state => (pair state).1) P).prod (Measure.map after P)
    rw [hpair_law, hfst_map, hsnd_map]
  have hsummary_factor : regenerativeSummary step (n + 1 + k) =
      regenerativeSummary step k ∘ after := by
    funext state
    simp only [regenerativeSummary, Function.comp_apply, after, pair, iter, tail]
    rw [show n + 1 + k = k + (n + 1) by omega,
      Function.iterate_add_apply, Function.iterate_succ_apply']
    rfl
  have hcomp := hpair_indep.comp measurable_id
    (measurable_regenerativeSummary step hstep k)
  change ProbabilityTheory.IndepFun (fun state => (pair state).1)
    (regenerativeSummary step (n + 1 + k)) P
  rw [hsummary_factor]
  simpa [Function.comp_def, pair, iter, regenerativeSummary] using hcomp

/-- Deterministic summaries of successive literal regenerative tails are
pairwise independent. -/
theorem regenerativeSummary_pairwise_indepFun
    {State Summary : Type*} [MeasurableSpace State] [MeasurableSpace Summary]
    (P : Measure State) [IsProbabilityMeasure P]
    (B : Measure Summary) [SFinite B]
    (step : State -> Summary × State) (hstep : Measurable step)
    (hstep_law : Measure.map step P = B.prod P) :
    Pairwise (fun n m => ProbabilityTheory.IndepFun
      (regenerativeSummary step n) (regenerativeSummary step m) P) := by
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · let k := m - (n + 1)
    have hmk : m = n + 1 + k := by
      dsimp [k]
      omega
    simpa [Function.onFun, hmk] using
      regenerativeSummary_indepFun_succ_add P B step hstep hstep_law n k
  · let k := n - (m + 1)
    have hnk : n = m + 1 + k := by
      dsimp [k]
      omega
    simpa [Function.onFun, hnk] using
      (regenerativeSummary_indepFun_succ_add P B step hstep hstep_law m k).symm

/-- All deterministic regenerative-tail summaries have the one-step summary
law. -/
theorem regenerativeSummary_identDistrib
    {State Summary : Type*} [MeasurableSpace State] [MeasurableSpace Summary]
    (P : Measure State) [IsProbabilityMeasure P]
    (B : Measure Summary) [SFinite B]
    (step : State -> Summary × State) (hstep : Measurable step)
    (hstep_law : Measure.map step P = B.prod P) (n : Nat) :
    ProbabilityTheory.IdentDistrib (regenerativeSummary step n)
      (regenerativeSummary step 0) P P := by
  refine ⟨(measurable_regenerativeSummary step hstep n).aemeasurable,
    (measurable_regenerativeSummary step hstep 0).aemeasurable, ?_⟩
  rw [regenerativeSummary_map_eq P B step hstep hstep_law n,
    regenerativeSummary_map_eq P B step hstep hstep_law 0]

end

end AppliedModelingLib.Probability

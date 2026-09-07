import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors
import AppliedModelingLib.Foundations.Probability.TwoSidedMarkedRenewalReward
import Mathlib.Tactic

/-!
# Finite literal head-tail factors for exponential renewal paths

This module exposes a finite initial block of a one-sided iid exponential
renewal path together with its untouched infinite tail.  The factor carrier is
recursive rather than a syntactic finite-product abbreviation: every displayed
head is a literal path coordinate, and the final leaf is the literal unused
tail.  This form supports replay inductions without treating a shifted path as
an independently supplied object.

No queueing, stationary-law, or tail claim is made here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A finite prefix of real coordinates, followed by the literal remaining
one-sided path.  At depth zero the factor is exactly the unconsumed path; at a
successor depth the first component is the next coordinate and the second
component is the remaining factor. -/
def finiteHeadTailCarrier : ℕ → Type
  | 0 => ℕ → ℝ
  | n + 1 => ℝ × finiteHeadTailCarrier n

instance finiteHeadTailCarrier.measurableSpace : (n : ℕ) →
    MeasurableSpace (finiteHeadTailCarrier n)
  | 0 => by
      change MeasurableSpace (ℕ → ℝ)
      infer_instance
  | n + 1 => by
      letI : MeasurableSpace (finiteHeadTailCarrier n) :=
        finiteHeadTailCarrier.measurableSpace n
      change MeasurableSpace (ℝ × finiteHeadTailCarrier n)
      infer_instance

/-- The law corresponding to `finiteHeadTailCarrier`: iid exponential heads
and an independent iid exponential unused tail. -/
def finiteHeadTailLaw (rate : ℝ) : (n : ℕ) → Measure (finiteHeadTailCarrier n)
  | 0 => exponentialInterarrivalMeasure rate
  | n + 1 => (expMeasure rate).prod (finiteHeadTailLaw rate n)

/-- Split the first `n` literal coordinates from a one-sided path, retaining
the unused suffix at the final leaf. -/
def finiteHeadTail : (n : ℕ) → (ℕ → ℝ) → finiteHeadTailCarrier n
  | 0 => id
  | n + 1 => fun f => (f 0, finiteHeadTail n (fun k => f (k + 1)))

/-- Read the finite displayed prefix from a finite head-tail factor. -/
def finiteHeadTailPrefix : (n : ℕ) → finiteHeadTailCarrier n → Fin n → ℝ
  | 0, _, i => Fin.elim0 i
  | n + 1, x, i =>
      Fin.cases x.1 (fun j => finiteHeadTailPrefix n x.2 j) i

/-- Read the unused infinite suffix from a finite head-tail factor. -/
def finiteHeadTailUnusedTail : (n : ℕ) → finiteHeadTailCarrier n → (ℕ → ℝ)
  | 0 => id
  | n + 1 => fun x => finiteHeadTailUnusedTail n x.2

theorem measurable_finiteHeadTail (n : ℕ) : Measurable (finiteHeadTail n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
      exact (measurable_pi_apply 0).prodMk
        (ih.comp (measurable_pi_iff.2 fun k => measurable_pi_apply (k + 1)))

/-- The first literal coordinate of a positive-depth finite head-tail factor
is the source path's coordinate at its current offset. -/
theorem finiteHeadTail_succ_head (n : ℕ) (f : ℕ → ℝ) :
    (finiteHeadTail (n + 1) f).1 = f 0 := by
  rfl

/-- Removing one displayed head advances the literal source path by one
coordinate. -/
theorem finiteHeadTail_succ_tail (n : ℕ) (f : ℕ → ℝ) :
    (finiteHeadTail (n + 1) f).2 =
      finiteHeadTail n (fun k => f (k + 1)) := by
  rfl

/-- Every finite displayed coordinate is the corresponding literal source
coordinate. -/
theorem finiteHeadTailPrefix_apply (n : ℕ) (f : ℕ → ℝ) (i : Fin n) :
    finiteHeadTailPrefix n (finiteHeadTail n f) i = f i := by
  induction n generalizing f with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simpa [finiteHeadTailPrefix, finiteHeadTail] using
          ih (fun k => f (k + 1)) j

/-- The final leaf is precisely the suffix of the source path beginning
after the displayed finite prefix. -/
theorem finiteHeadTailUnusedTail_apply (n : ℕ) (f : ℕ → ℝ) :
    finiteHeadTailUnusedTail n (finiteHeadTail n f) =
      fun k => f (n + k) := by
  induction n generalizing f with
  | zero =>
      funext k
      simp [finiteHeadTailUnusedTail, finiteHeadTail]
  | succ n ih =>
      change finiteHeadTailUnusedTail n
          (finiteHeadTail n (fun j => f (j + 1))) =
        fun k => f ((n + 1) + k)
      rw [ih]
      funext k
      congr 1
      omega

/-- A finite literal prefix and its unconsumed suffix have exactly the
recursive iid exponential product law. -/
theorem map_finiteHeadTail_exponentialInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    Measure.map (finiteHeadTail n) (exponentialInterarrivalMeasure rate) =
      finiteHeadTailLaw rate n := by
  induction n with
  | zero =>
      exact Measure.map_id
  | succ n ih =>
      letI : IsProbabilityMeasure (expMeasure rate) :=
        isProbabilityMeasure_expMeasure hrate
      letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
        isProbabilityMeasure_exponentialInterarrivalMeasure hrate
      change Measure.map (finiteHeadTail (n + 1))
          (exponentialInterarrivalMeasure rate) =
        (expMeasure rate).prod (finiteHeadTailLaw rate n)
      calc
        Measure.map (finiteHeadTail (n + 1))
            (exponentialInterarrivalMeasure rate) =
            Measure.map (Prod.map id (finiteHeadTail n))
              (Measure.map headTail (exponentialInterarrivalMeasure rate)) := by
              rw [Measure.map_map
                (measurable_id.prodMap (measurable_finiteHeadTail n))
                measurable_headTail]
              rfl
        _ = Measure.map (Prod.map id (finiteHeadTail n))
              ((expMeasure rate).prod (exponentialInterarrivalMeasure rate)) := by
              rw [map_headTail_exponentialInterarrivalMeasure hrate]
        _ = (expMeasure rate).prod (finiteHeadTailLaw rate n) := by
              rw [← Measure.map_prod_map _ _ measurable_id
                (measurable_finiteHeadTail n), Measure.map_id, ih]

/-- The finite-prefix-with-tail law is a probability law whenever the common
exponential rate is positive. -/
theorem isProbabilityMeasure_finiteHeadTailLaw
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    IsProbabilityMeasure (finiteHeadTailLaw rate n) := by
  induction n with
  | zero => exact isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  | succ n ih =>
      letI : IsProbabilityMeasure (expMeasure rate) :=
        isProbabilityMeasure_expMeasure hrate
      letI : IsProbabilityMeasure (finiteHeadTailLaw rate n) := ih
      change IsProbabilityMeasure
        ((expMeasure rate).prod (finiteHeadTailLaw rate n))
      infer_instance

/-- Split the literal negative-index half of a two-sided path into its first
`n` negative coordinates and the remaining older negative tail.  Central and
positive coordinates are not retained in this factor. -/
def twoSidedNegativeFiniteHeadTail (n : ℕ) (ω : ℤ → ℝ) :
    finiteHeadTailCarrier n :=
  finiteHeadTail n (twoSidedHeadPositiveNegative ω).2

theorem measurable_twoSidedNegativeFiniteHeadTail (n : ℕ) :
    Measurable (twoSidedNegativeFiniteHeadTail n) := by
  exact (measurable_finiteHeadTail n).comp
    (measurable_snd.comp measurable_twoSidedHeadPositiveNegative)

/-- The displayed negative prefix is indexed by the literal past coordinates
`-1, -2, ...`, with no recentered path hidden in the statement. -/
theorem twoSidedNegativeFiniteHeadTailPrefix_apply
    (n : ℕ) (ω : ℤ → ℝ) (i : Fin n) :
    finiteHeadTailPrefix n (twoSidedNegativeFiniteHeadTail n ω) i =
      twoSidedGap (Int.negSucc i) ω := by
  unfold twoSidedNegativeFiniteHeadTail
  rw [finiteHeadTailPrefix_apply]
  rfl

/-- The unused tail begins strictly after the displayed negative prefix. -/
theorem twoSidedNegativeFiniteHeadTailUnusedTail_apply
    (n : ℕ) (ω : ℤ → ℝ) :
    finiteHeadTailUnusedTail n (twoSidedNegativeFiniteHeadTail n ω) =
      fun k => twoSidedGap (Int.negSucc (n + k)) ω := by
  unfold twoSidedNegativeFiniteHeadTail
  rw [finiteHeadTailUnusedTail_apply]
  rfl

/-- The literal negative finite prefix and its older unused tail have their
exact iid exponential factor law under the two-sided Palm path. -/
theorem map_twoSidedNegativeFiniteHeadTail_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    Measure.map (twoSidedNegativeFiniteHeadTail n)
      (twoSidedInterarrivalMeasure rate) = finiteHeadTailLaw rate n := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hnegative :
      Measure.map (fun ω : ℤ → ℝ => (twoSidedHeadPositiveNegative ω).2)
        (twoSidedInterarrivalMeasure rate) =
        exponentialInterarrivalMeasure rate := by
    calc
      Measure.map (fun ω : ℤ → ℝ => (twoSidedHeadPositiveNegative ω).2)
          (twoSidedInterarrivalMeasure rate) =
          Measure.map Prod.snd
            (Measure.map twoSidedHeadPositiveNegative
              (twoSidedInterarrivalMeasure rate)) := by
            rw [Measure.map_map measurable_snd
              measurable_twoSidedHeadPositiveNegative]
            rfl
      _ = Measure.map Prod.snd
          (((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
            (exponentialInterarrivalMeasure rate)) := by
            rw [map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure hrate]
      _ = exponentialInterarrivalMeasure rate := by
            rw [Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map (twoSidedNegativeFiniteHeadTail n)
        (twoSidedInterarrivalMeasure rate) =
        Measure.map (finiteHeadTail n)
          (Measure.map (fun ω : ℤ → ℝ =>
            (twoSidedHeadPositiveNegative ω).2)
            (twoSidedInterarrivalMeasure rate)) := by
            unfold twoSidedNegativeFiniteHeadTail
            let g : (ℤ → ℝ) → (ℕ → ℝ) :=
              fun ω => (twoSidedHeadPositiveNegative ω).2
            have hg : Measurable g :=
              measurable_snd.comp measurable_twoSidedHeadPositiveNegative
            have hcompose :
                (fun ω : ℤ → ℝ => finiteHeadTail n
                  (twoSidedHeadPositiveNegative ω).2) =
                  finiteHeadTail n ∘ g := by
              rfl
            rw [hcompose]
            exact (Measure.map_map (measurable_finiteHeadTail n) hg).symm
    _ = Measure.map (finiteHeadTail n) (exponentialInterarrivalMeasure rate) := by
          rw [hnegative]
    _ = finiteHeadTailLaw rate n :=
          map_finiteHeadTail_exponentialInterarrivalMeasure hrate n

/-- Factor the literal negative past of both the arrival-gap path and the
independent work-mark path.  Each component retains its own unused older
tail, so no finite block is silently substituted for the full source path. -/
def markedRenewalFinitePastHeadTailFactors (n : ℕ)
    (z : TwoSidedMarkedRenewalSample) :
    finiteHeadTailCarrier n × finiteHeadTailCarrier n :=
  (twoSidedNegativeFiniteHeadTail n z.1,
    twoSidedNegativeFiniteHeadTail n z.2)

theorem measurable_markedRenewalFinitePastHeadTailFactors (n : ℕ) :
    Measurable (markedRenewalFinitePastHeadTailFactors n) := by
  exact ((measurable_twoSidedNegativeFiniteHeadTail n).comp measurable_fst).prodMk
    ((measurable_twoSidedNegativeFiniteHeadTail n).comp measurable_snd)

/-- Coordinate form for the displayed literal past interarrival gaps. -/
theorem markedRenewalFinitePastHeadTailFactors_gap_apply
    (n : ℕ) (z : TwoSidedMarkedRenewalSample) (i : Fin n) :
    finiteHeadTailPrefix n (markedRenewalFinitePastHeadTailFactors n z).1 i =
      twoSidedGap (Int.negSucc i) z.1 := by
  exact twoSidedNegativeFiniteHeadTailPrefix_apply n z.1 i

/-- Coordinate form for the displayed literal past work marks. -/
theorem markedRenewalFinitePastHeadTailFactors_work_apply
    (n : ℕ) (z : TwoSidedMarkedRenewalSample) (i : Fin n) :
    finiteHeadTailPrefix n (markedRenewalFinitePastHeadTailFactors n z).2 i =
      twoSidedGap (Int.negSucc i) z.2 := by
  exact twoSidedNegativeFiniteHeadTailPrefix_apply n z.2 i

/-- The first unused factor leaf is the strictly older arrival-gap tail. -/
theorem markedRenewalFinitePastHeadTailFactors_gap_unusedTail_apply
    (n : ℕ) (z : TwoSidedMarkedRenewalSample) :
    finiteHeadTailUnusedTail n (markedRenewalFinitePastHeadTailFactors n z).1 =
      fun k => twoSidedGap (Int.negSucc (n + k)) z.1 := by
  exact twoSidedNegativeFiniteHeadTailUnusedTail_apply n z.1

/-- The second unused factor leaf is the strictly older work-mark tail. -/
theorem markedRenewalFinitePastHeadTailFactors_work_unusedTail_apply
    (n : ℕ) (z : TwoSidedMarkedRenewalSample) :
    finiteHeadTailUnusedTail n (markedRenewalFinitePastHeadTailFactors n z).2 =
      fun k => twoSidedGap (Int.negSucc (n + k)) z.2 := by
  exact twoSidedNegativeFiniteHeadTailUnusedTail_apply n z.2

/-- Exact product law for the finite literal negative marked block and its
two unused tails.  The first factor is the arrival-gap block (rate `rate`),
the second is the work-mark block (unit rate). -/
theorem map_markedRenewalFinitePastHeadTailFactors_twoSidedMarkedRenewalMeasure
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    Measure.map (markedRenewalFinitePastHeadTailFactors n)
      (twoSidedMarkedRenewalMeasure rate) =
      (finiteHeadTailLaw rate n).prod (finiteHeadTailLaw (1 : ℝ) n) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  change Measure.map
      (Prod.map (twoSidedNegativeFiniteHeadTail n)
        (twoSidedNegativeFiniteHeadTail n))
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) = _
  rw [← Measure.map_prod_map _ _
    (measurable_twoSidedNegativeFiniteHeadTail n)
    (measurable_twoSidedNegativeFiniteHeadTail n),
    map_twoSidedNegativeFiniteHeadTail_twoSidedInterarrivalMeasure hrate n,
    map_twoSidedNegativeFiniteHeadTail_twoSidedInterarrivalMeasure (by norm_num) n]

/-- Adjoin any independent initial state to the literal finite marked-past
factorization.  This is the direct product interface used by causal replay
inductions. -/
theorem map_initial_markedRenewalFinitePastHeadTailFactors
    {Ω : Type*} [MeasurableSpace Ω] (initialLaw : Measure Ω)
    [IsProbabilityMeasure initialLaw]
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    Measure.map
      (Prod.map id (markedRenewalFinitePastHeadTailFactors n))
      (initialLaw.prod (twoSidedMarkedRenewalMeasure rate)) =
      initialLaw.prod
        ((finiteHeadTailLaw rate n).prod (finiteHeadTailLaw (1 : ℝ) n)) := by
  letI : IsProbabilityMeasure (twoSidedMarkedRenewalMeasure rate) := by
    change IsProbabilityMeasure
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
    infer_instance
  rw [← Measure.map_prod_map _ _ measurable_id
    (measurable_markedRenewalFinitePastHeadTailFactors n), Measure.map_id,
    map_markedRenewalFinitePastHeadTailFactors_twoSidedMarkedRenewalMeasure hrate n]

end

end AppliedModelingLib.Probability.PoissonProcess

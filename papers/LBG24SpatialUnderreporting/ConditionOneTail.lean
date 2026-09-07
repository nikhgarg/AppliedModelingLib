import AppliedModelingLib.Foundations.Probability.ForwardStoppedPoisson
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicNoArrival
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Condexp

/-!
# Condition 1 selection and post-start Poisson tails

This module keeps three distinct layers of the Appendix B.2 random-start
argument explicit.

* `Theorem2ConditionOneSelection` is a kernelized, source-faithful repair of
  the paper's Condition 1: conditional on the first report, the selected start
  has a caller-shared conditional kernel, lies after that report, and is
  conditionally independent of a caller-supplied representation of the
  post-first-report path.
* The `Theorem2ConditionOneSelection` namespace proves the corrected Lemma 2
  bridge from an explicit full-tail conditional kernel and a deterministic
  offset count law.  This derives, rather than assumes, the conditional
  post-start Poisson law given `σ(T₁,S)` and then `σ(T₁)`.
* `Theorem2ConditionOnePostStartTailFactorizationCertificate` packages an atom
  factorization combining the source selection premise, post-first-report
  Poisson regeneration, and the random time-shift argument.

The statements here concern conditioning on the displayed report variables,
not an arbitrary stopped filtration.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal

noncomputable section

/--
Kernelized selection portion of the paper's Condition 1.  The source writes a
density-style `g(t)` despite conditioning on a continuously valued `T₁`; this
record uses the well-typed conditional kernel `g(· | T₁)` instead.  The source
states that the selected start lies in `[T₁,T]`, so the observation horizon is
recorded explicitly. In a family indexed by the Poisson rate, callers must
reuse `rateFreeStartKernel` across rates. The existing algebraic
`Theorem2ConditionOneSource` separately records the rate-independent
fixed-history likelihood term.

`start_condIndep_postFirstReportTail` is the precise Lean interpretation of
the source phrase that the selected start is independent, conditional on
`T₁`, of the caller-supplied post-`T₁` tail representation.
-/
structure Theorem2ConditionOneSelection
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tail : Type*) [MeasurableSpace Tail] where
  firstReportTime : Ω → ℝ≥0
  startTime : Ω → ℝ≥0
  /-- The source observation horizon `T`. -/
  observationHorizon : ℝ≥0
  /-- A caller-supplied measurable representation of the post-`T₁` tail. -/
  postFirstReportTail : Ω → Tail
  rateFreeStartKernel : Kernel ℝ≥0 ℝ≥0
  rateFreeStartKernel_isMarkov : IsMarkovKernel rateFreeStartKernel
  firstReportTime_measurable : Measurable firstReportTime
  startTime_measurable : Measurable startTime
  postFirstReportTail_measurable : Measurable postFirstReportTail
  firstReport_le_start : ∀ ω, firstReportTime ω ≤ startTime ω
  start_le_observationHorizon : ∀ ω, startTime ω ≤ observationHorizon
  start_conditional_law : ∀ᵐ ω ∂P,
    ProbabilityTheory.HasLaw startTime
      (rateFreeStartKernel (firstReportTime ω))
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap firstReportTime inferInstance) ω)
  rateFreeStartKernel_supported_after_first : ∀ t : ℝ≥0,
    rateFreeStartKernel t (Set.Ici t) = 1
  start_condIndep_postFirstReportTail :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap firstReportTime inferInstance)
      firstReportTime_measurable.comap_le
      startTime postFirstReportTail P

namespace Theorem2ConditionOneSelection

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The source-relevant selection sigma-algebra `σ(T₁, S)`. -/
abbrev selectionSigma
    {Tail : Type*} [MeasurableSpace Tail]
    (C : Theorem2ConditionOneSelection Ω P Tail) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (C.firstReportTime ω, C.startTime ω)) inferInstance

theorem selection_measurable
    {Tail : Type*} [MeasurableSpace Tail]
    (C : Theorem2ConditionOneSelection Ω P Tail) :
    Measurable fun ω => (C.firstReportTime ω, C.startTime ω) :=
  C.firstReportTime_measurable.prodMk C.startTime_measurable

/-- No canonical renewal in the horizon `u` after the deterministic offset
`s - t` of a fresh post-first-report tail.  The real-valued offset makes this
definition measurable on all pairs; the only uses below impose `t ≤ s`. -/
def canonicalTailNoArrival
    (u : ℝ≥0) (p : ℝ≥0 × ℝ≥0) (tail : ℕ → ℝ) : Prop :=
  canonicalRenewalCount (((p.2 : ℝ) - (p.1 : ℝ)) + (u : ℝ)) tail =
    canonicalRenewalCount ((p.2 : ℝ) - (p.1 : ℝ)) tail

/-- Measurability of the canonical no-arrival event when the selected offset
and the fresh tail are both variable. -/
theorem measurable_canonicalTailNoArrival (u : ℝ≥0) :
    Measurable fun x : (ℝ≥0 × ℝ≥0) × (ℕ → ℝ) =>
      canonicalTailNoArrival u x.1 x.2 := by
  let d : (ℝ≥0 × ℝ≥0) × (ℕ → ℝ) → ℝ :=
    fun x => (x.1.2 : ℝ) - (x.1.1 : ℝ)
  have hd : Measurable d := by
    exact (measurable_fst.snd.coe_nnreal_real).sub
      (measurable_fst.fst.coe_nnreal_real)
  have hleft : Measurable fun x : (ℝ≥0 × ℝ≥0) × (ℕ → ℝ) =>
      canonicalRenewalCount (d x + (u : ℝ)) x.2 := by
    exact measurable_canonicalRenewalCount_joint.comp
      ((hd.add measurable_const).prodMk measurable_snd)
  have hright : Measurable fun x : (ℝ≥0 × ℝ≥0) × (ℕ → ℝ) =>
      canonicalRenewalCount (d x) x.2 := by
    exact measurable_canonicalRenewalCount_joint.comp (hd.prodMk measurable_snd)
  simpa only [canonicalTailNoArrival, d] using hleft.eq hright

/-- The fresh canonical tail has the no-arrival survival probability at every
deterministic offset. -/
theorem canonicalTailNoArrival_real
    {rate : ℝ} (hrate : 0 < rate) (u t s : ℝ≥0) (hts : t ≤ s) :
    (exponentialInterarrivalMeasure rate).real
        {tail | canonicalTailNoArrival u (t, s) tail} =
      noArrivalProb rate (u : ℝ) := by
  have hdelay : 0 ≤ (s : ℝ) - (t : ℝ) := by
    exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts)
  simpa only [canonicalTailNoArrival, noArrivalProb] using
    canonicalRenewalCount_same_increment_real_eq_exp hrate
      (s := (s : ℝ) - (t : ℝ)) (h := (u : ℝ))
      hdelay (NNReal.coe_nonneg _)

/--
Event-level corrected Lemma-2 bridge from a concrete full post-first-report
tail kernel.  This is the zero-only counterpart of the count-law bridge
below: instead of requiring every atom of a count distribution, it needs only
the common probability of a measurable tail event at every deterministic
offset.  It proves the event law given `σ(T₁,S)`.
-/
theorem conditional_postTailEvent_real_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (postEvent : (ℝ≥0 × ℝ≥0) → Tail → Prop)
    (hpostEvent : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postEvent p.1 p.2)
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (q : ℝ)
    (htailLaw : ∀ (t s : ℝ≥0), t ≤ s →
      (K t).real {r | postEvent (t, s) r} = q) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | postEvent (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω')} = q := by
  let X : Ω → ℝ≥0 × ℝ≥0 := fun ω => (C.firstReportTime ω, C.startTime ω)
  let R : Ω → Tail := C.postFirstReportTail
  let E : Set ((ℝ≥0 × ℝ≥0) × Tail) :=
    {p | postEvent p.1 p.2}
  let f : (ℝ≥0 × ℝ≥0) × Tail → ℝ := E.indicator fun _ => (1 : ℝ)
  have hX : Measurable X := C.selection_measurable
  have hR : Measurable R := C.postFirstReportTail_measurable
  have hE : MeasurableSet E := by
    have hEeq : E = (fun p : (ℝ≥0 × ℝ≥0) × Tail => postEvent p.1 p.2) ⁻¹' {True} := by
      ext p
      simp [E]
    rw [hEeq]
    exact hpostEvent (measurableSet_singleton True)
  have hf : StronglyMeasurable f :=
    (measurable_const.indicator hE).stronglyMeasurable
  have hER : MeasurableSet {ω : Ω | postEvent
      (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω)} := by
    simpa only [X, R, E, Set.preimage_setOf_eq] using hE.preimage (hX.prodMk hR)
  have hf_int : Integrable (fun ω => f (X ω, R ω)) P := by
    simpa only [f, E, Set.indicator, Set.mem_setOf_eq,
      Set.preimage_setOf_eq] using (integrable_const (1 : ℝ)).indicator hER
  have hcondDistrib :
      ProbabilityTheory.condDistrib R X P =ᵐ[P.map X]
        (ProbabilityTheory.condDistrib R C.firstReportTime P).prodMkRight ℝ≥0 := by
    exact
      (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
        (f := R) (g := C.startTime)
        C.postFirstReportTail_measurable C.startTime_measurable
        C.firstReportTime_measurable).mp
        C.start_condIndep_postFirstReportTail
  have hcondDistrib' : ∀ᵐ ω ∂P,
      ProbabilityTheory.condDistrib R X P (X ω) =
        (ProbabilityTheory.condDistrib R C.firstReportTime P).prodMkRight ℝ≥0 (X ω) := by
    exact MeasureTheory.ae_of_ae_map hX.aemeasurable hcondDistrib
  have hTailKernel' : ∀ᵐ ω ∂P,
      ProbabilityTheory.condDistrib R C.firstReportTime P (C.firstReportTime ω) =
        K (C.firstReportTime ω) := by
    exact MeasureTheory.ae_of_ae_map C.firstReportTime_measurable.aemeasurable hTailKernel
  have hcondExp := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
    (μ := P) (X := X) (Y := R) hX hR.aemeasurable hf hf_int
  have hle : C.selectionSigma ≤ ‹MeasurableSpace Ω› := by
    simpa only [selectionSigma] using hX.comap_le
  letI : IsFiniteMeasure (P.trim hle) := MeasureTheory.isFiniteMeasure_trim hle
  have hkernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
        {ω' | postEvent (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω')}) =ᵐ[P]
      P[{ω' | postEvent (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω')}.indicator fun _ => (1 : ℝ) |
        C.selectionSigma] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hle hER
  filter_upwards [hcondExp, hcondDistrib', hTailKernel', hkernel] with ω hce hdist htail hkern
  have htailLawω :
      (K (C.firstReportTime ω)).real
          {r | postEvent (C.firstReportTime ω, C.startTime ω) r} = q :=
    htailLaw (C.firstReportTime ω) (C.startTime ω) (C.firstReport_le_start ω)
  have hintegral :
      (∫ r, f (X ω, r) ∂ProbabilityTheory.condDistrib R X P (X ω)) = q := by
    rw [hdist]
    change ∫ r, f (X ω, r) ∂
      ProbabilityTheory.condDistrib R C.firstReportTime P (C.firstReportTime ω) = q
    rw [htail]
    let Eω : Set Tail := {r | postEvent (C.firstReportTime ω, C.startTime ω) r}
    have hEω : MeasurableSet Eω := by
      have hEωeq : Eω = (fun r : Tail => ((C.firstReportTime ω, C.startTime ω), r)) ⁻¹' E := by
        ext r
        simp [Eω, E]
      rw [hEωeq]
      exact hE.preimage (measurable_const.prodMk measurable_id)
    have hfeq : (fun r : Tail => f (X ω, r)) = Eω.indicator (fun _ => (1 : ℝ)) := by
      funext r
      by_cases h : postEvent (C.firstReportTime ω, C.startTime ω) r <;>
        simp [f, E, Eω, X, h]
    rw [hfeq, integral_indicator hEω, setIntegral_const, smul_eq_mul, mul_one]
    simpa only [Eω] using htailLawω
  have hfun :
      (fun a : Ω => f (X a, R a)) =
        {a | postEvent (C.firstReportTime a, C.startTime a)
          (C.postFirstReportTail a)}.indicator fun _ => (1 : ℝ) := by
    funext a
    by_cases h : postEvent (C.firstReportTime a, C.startTime a)
        (C.postFirstReportTail a) <;>
      simp [f, E, X, R, h]
  change (ProbabilityTheory.condExpKernel P
      (MeasurableSpace.comap X inferInstance) ω).real
      {ω' | postEvent (C.firstReportTime ω', C.startTime ω')
        (C.postFirstReportTail ω')} = q
  calc
    (ProbabilityTheory.condExpKernel P (MeasurableSpace.comap X inferInstance) ω).real
        {ω' | postEvent (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω')} =
        P[{ω' | postEvent (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω')}.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap X inferInstance] ω := hkern
    _ = P[fun a => f (X a, R a) | MeasurableSpace.comap X inferInstance] ω := by
      rw [hfun]
    _ = ∫ r, f (X ω, r) ∂ProbabilityTheory.condDistrib R X P (X ω) := hce
    _ = q := hintegral

/-- The event-level bridge after forgetting the selected start and conditioning
only on the first report. -/
theorem conditional_postTailEvent_real_given_firstReport_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (postEvent : (ℝ≥0 × ℝ≥0) → Tail → Prop)
    (hpostEvent : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postEvent p.1 p.2)
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (q : ℝ)
    (htailLaw : ∀ (t s : ℝ≥0), t ≤ s →
      (K t).real {r | postEvent (t, s) r} = q) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | postEvent (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω')} = q := by
  let X : Ω → ℝ≥0 × ℝ≥0 := fun ω => (C.firstReportTime ω, C.startTime ω)
  let R : Ω → Tail := C.postFirstReportTail
  let A : Set Ω := {ω | postEvent (X ω) (R ω)}
  have hX : Measurable X := C.selection_measurable
  have hR : Measurable R := C.postFirstReportTail_measurable
  have hA : MeasurableSet A := by
    have hAeq : A = (fun ω : Ω => postEvent (X ω) (R ω)) ⁻¹' {True} := by
      ext ω
      simp [A]
    rw [hAeq]
    exact (hpostEvent.comp (hX.prodMk hR)) (measurableSet_singleton True)
  have hfirstle_selection :
      MeasurableSpace.comap C.firstReportTime inferInstance ≤ C.selectionSigma := by
    have hpair : Measurable[C.selectionSigma]
        (fun ω => (C.firstReportTime ω, C.startTime ω)) := comap_measurable _
    exact (measurable_fst.comp hpair).comap_le
  have hselectionle : C.selectionSigma ≤ ‹MeasurableSpace Ω› := by
    simpa only [Theorem2ConditionOneSelection.selectionSigma] using hX.comap_le
  have hfirstle : MeasurableSpace.comap C.firstReportTime inferInstance ≤
      ‹MeasurableSpace Ω› := C.firstReportTime_measurable.comap_le
  letI : IsFiniteMeasure (P.trim hselectionle) :=
    MeasureTheory.isFiniteMeasure_trim hselectionle
  have hselectionKernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real A) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hselectionle hA
  have hselectionEvent : ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real A = q := by
    simpa only [X, R, A] using
      C.conditional_postTailEvent_real_of_tailKernel postEvent hpostEvent K
        hTailKernel q htailLaw
  have hselectionCondExp :
      P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] =ᵐ[P]
        fun _ => q :=
    hselectionKernel.symm.trans hselectionEvent
  have htower :
      P[P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] |
        MeasurableSpace.comap C.firstReportTime inferInstance] =ᵐ[P]
        P[A.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap C.firstReportTime inferInstance] :=
    condExp_condExp_of_le hfirstle_selection hselectionle
  have hfirstCondExp :
      P[A.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap C.firstReportTime inferInstance] =ᵐ[P]
        fun _ => q := by
    calc
      P[A.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap C.firstReportTime inferInstance] =ᵐ[P]
          P[P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] |
            MeasurableSpace.comap C.firstReportTime inferInstance] :=
        htower.symm
      _ =ᵐ[P] P[fun _ : Ω => q |
          MeasurableSpace.comap C.firstReportTime inferInstance] :=
        condExp_congr_ae hselectionCondExp
      _ =ᵐ[P] fun _ => q := by
        rw [condExp_const hfirstle]
  have hfirstKernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real A) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) |
        MeasurableSpace.comap C.firstReportTime inferInstance] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hfirstle hA
  simpa only [X, R, A] using hfirstKernel.trans hfirstCondExp

/-- A random Condition-1 selected start has the canonical no-arrival tail
when the post-first-report conditional tail kernel is the fresh exponential
interarrival law. -/
theorem conditional_canonicalTailNoArrival_real_of_tailKernel
    {rate : ℝ} (hrate : 0 < rate)
    (C : Theorem2ConditionOneSelection Ω P (ℕ → ℝ))
    (u : ℝ≥0)
    (K : Kernel ℝ≥0 (ℕ → ℝ)) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (hK : ∀ t : ℝ≥0, K t = exponentialInterarrivalMeasure rate) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | canonicalTailNoArrival u
            (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω')} =
        noArrivalProb rate (u : ℝ) := by
  apply C.conditional_postTailEvent_real_of_tailKernel
    (canonicalTailNoArrival u)
    (measurable_canonicalTailNoArrival u) K hTailKernel
    (noArrivalProb rate (u : ℝ))
  intro t s hts
  rw [hK t]
  exact canonicalTailNoArrival_real hrate u t s hts

/-- The same canonical no-arrival law after conditioning only on the first
report, which is the conditioning level of the source's Lemma 2. -/
theorem conditional_canonicalTailNoArrival_real_given_firstReport_of_tailKernel
    {rate : ℝ} (hrate : 0 < rate)
    (C : Theorem2ConditionOneSelection Ω P (ℕ → ℝ))
    (u : ℝ≥0)
    (K : Kernel ℝ≥0 (ℕ → ℝ)) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (hK : ∀ t : ℝ≥0, K t = exponentialInterarrivalMeasure rate) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | canonicalTailNoArrival u
            (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω')} =
        noArrivalProb rate (u : ℝ) := by
  apply C.conditional_postTailEvent_real_given_firstReport_of_tailKernel
    (canonicalTailNoArrival u)
    (measurable_canonicalTailNoArrival u) K hTailKernel
    (noArrivalProb rate (u : ℝ))
  intro t s hts
  rw [hK t]
  exact canonicalTailNoArrival_real hrate u t s hts

/-- Paper-facing no-report form of the canonical tail bridge.  The
representation premise is the remaining link from the caller's forward count
path to the canonical post-first-report tail. -/
theorem conditional_postStartCount_zero_real_of_canonicalTailKernel
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOneSelection Ω P (ℕ → ℝ))
    (u : ℝ≥0)
    (hrepresentation : ∀ ω,
      forwardPostStopIntervalCount H C.startTime u ω = 0 ↔
        canonicalTailNoArrival u
          (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω))
    (K : Kernel ℝ≥0 (ℕ → ℝ)) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (hK : ∀ t : ℝ≥0, K t = exponentialInterarrivalMeasure H.rate) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) := by
  have hevent :
      {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        {ω' | canonicalTailNoArrival u
          (C.firstReportTime ω', C.startTime ω') (C.postFirstReportTail ω')} := by
    ext ω'
    exact hrepresentation ω'
  rw [hevent]
  exact C.conditional_canonicalTailNoArrival_real_of_tailKernel
    H.rate_pos u K hTailKernel hK

/-- The paper-facing canonical-tail no-report law conditioned only on the
first report. -/
theorem conditional_postStartCount_zero_real_given_firstReport_of_canonicalTailKernel
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOneSelection Ω P (ℕ → ℝ))
    (u : ℝ≥0)
    (hrepresentation : ∀ ω,
      forwardPostStopIntervalCount H C.startTime u ω = 0 ↔
        canonicalTailNoArrival u
          (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω))
    (K : Kernel ℝ≥0 (ℕ → ℝ)) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (hK : ∀ t : ℝ≥0, K t = exponentialInterarrivalMeasure H.rate) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) := by
  have hevent :
      {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        {ω' | canonicalTailNoArrival u
          (C.firstReportTime ω', C.startTime ω') (C.postFirstReportTail ω')} := by
    ext ω'
    exact hrepresentation ω'
  rw [hevent]
  exact C.conditional_canonicalTailNoArrival_real_given_firstReport_of_tailKernel
    H.rate_pos u K hTailKernel hK

/-- On the canonical iid exponential path, a Condition-1 selection whose
first-report and tail fields are the actual first arrival and its future tail
has the constant fresh-tail kernel required by the preceding bridge.  The
selection itself remains an explicit Condition-1 input. -/
theorem canonicalFirstArrivalSelection_tailKernel
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ProbabilityTheory.condDistrib C.postFirstReportTail C.firstReportTime
          (exponentialInterarrivalMeasure rate) =ᵐ[
            (exponentialInterarrivalMeasure rate).map C.firstReportTime]
          Kernel.const ℝ≥0 (exponentialInterarrivalMeasure rate) := by
  intro C hfirst htail
  simpa only [hfirst, htail] using
    canonicalFirstArrival_toNNReal_condDistrib_futureInterarrival_eq_const hrate

/-- Concrete canonical-first-report instance of the selected-start
no-arrival bridge, conditional on the selection sigma-algebra `σ(T₁,S)`. -/
theorem conditional_canonicalTailNoArrival_real_of_canonicalFirstArrival
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ u : ℝ≥0, ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
        (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
          C.selectionSigma ω).real
            {ω' | canonicalTailNoArrival u
              (C.firstReportTime ω', C.startTime ω')
              (C.postFirstReportTail ω')} =
          noArrivalProb rate (u : ℝ) := by
  intro C hfirst htail u
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  exact C.conditional_canonicalTailNoArrival_real_of_tailKernel hrate u
    (Kernel.const ℝ≥0 (exponentialInterarrivalMeasure rate))
    (canonicalFirstArrivalSelection_tailKernel hrate C hfirst htail)
    (fun _ => rfl)

/-- Concrete canonical-first-report instance after forgetting the selected
start and conditioning only on the first report, as in the source's Lemma 2.
-/
theorem conditional_canonicalTailNoArrival_real_given_firstReport_of_canonicalFirstArrival
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ u : ℝ≥0, ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
        (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
          (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
            {ω' | canonicalTailNoArrival u
              (C.firstReportTime ω', C.startTime ω')
              (C.postFirstReportTail ω')} =
          noArrivalProb rate (u : ℝ) := by
  intro C hfirst htail u
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  exact C.conditional_canonicalTailNoArrival_real_given_firstReport_of_tailKernel hrate u
    (Kernel.const ℝ≥0 (exponentialInterarrivalMeasure rate))
    (canonicalFirstArrivalSelection_tailKernel hrate C hfirst htail)
    (fun _ => rfl)

/--
Corrected Lemma-2 atom bridge from a concrete full post-first-report tail
kernel.  Besides Condition 1's conditional independence, this requires a
path-complete tail representation, its regular conditional kernel given
`T₁`, and its deterministic-offset Poisson count law.  It proves the
residual-count law given `σ(T₁,S)` only; it is not a history-level result for
the paper's full Appendix Theorem 2.
-/
theorem conditional_postTailCount_atom_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (postCount : (ℝ≥0 × ℝ≥0) → Tail → ℕ)
    (hpostCount : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postCount p.1 p.2)
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (htailLaw : ∀ (t s : ℝ≥0) (k : ℕ), t ≤ s →
      (K t).real {r | postCount (t, s) r = k} = ν.real {k})
    (k : ℕ) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | postCount (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω') = k} =
        ν.real {k} := by
  let X : Ω → ℝ≥0 × ℝ≥0 := fun ω => (C.firstReportTime ω, C.startTime ω)
  let R : Ω → Tail := C.postFirstReportTail
  let E : Set ((ℝ≥0 × ℝ≥0) × Tail) :=
    {p | postCount p.1 p.2 = k}
  let f : (ℝ≥0 × ℝ≥0) × Tail → ℝ := E.indicator fun _ => (1 : ℝ)
  have hX : Measurable X := C.selection_measurable
  have hR : Measurable R := C.postFirstReportTail_measurable
  have hE : MeasurableSet E := by
    simpa only [E, Set.preimage_setOf_eq] using hpostCount (measurableSet_singleton k)
  have hf : StronglyMeasurable f :=
    (measurable_const.indicator hE).stronglyMeasurable
  have hER : MeasurableSet {ω : Ω | postCount (C.firstReportTime ω, C.startTime ω)
      (C.postFirstReportTail ω) = k} := by
    simpa only [X, R, E, Set.preimage_setOf_eq] using
      hE.preimage (hX.prodMk hR)
  have hf_int : Integrable (fun ω => f (X ω, R ω)) P := by
    simpa only [f, E, Set.indicator, Set.mem_setOf_eq,
      Set.preimage_setOf_eq] using (integrable_const (1 : ℝ)).indicator hER
  have hcondDistrib :
      ProbabilityTheory.condDistrib R X P =ᵐ[P.map X]
        (ProbabilityTheory.condDistrib R C.firstReportTime P).prodMkRight ℝ≥0 := by
    exact
      (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
        (f := R) (g := C.startTime)
        C.postFirstReportTail_measurable C.startTime_measurable
        C.firstReportTime_measurable).mp
        C.start_condIndep_postFirstReportTail
  have hcondDistrib' : ∀ᵐ ω ∂P,
      ProbabilityTheory.condDistrib R X P (X ω) =
        (ProbabilityTheory.condDistrib R C.firstReportTime P).prodMkRight ℝ≥0 (X ω) := by
    exact MeasureTheory.ae_of_ae_map hX.aemeasurable hcondDistrib
  have hTailKernel' : ∀ᵐ ω ∂P,
      ProbabilityTheory.condDistrib R C.firstReportTime P (C.firstReportTime ω) =
        K (C.firstReportTime ω) := by
    exact MeasureTheory.ae_of_ae_map C.firstReportTime_measurable.aemeasurable hTailKernel
  have hcondExp := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
    (μ := P) (X := X) (Y := R) hX hR.aemeasurable hf hf_int
  have hle : C.selectionSigma ≤ ‹MeasurableSpace Ω› := by
    simpa only [selectionSigma] using hX.comap_le
  letI : IsFiniteMeasure (P.trim hle) := MeasureTheory.isFiniteMeasure_trim hle
  have hkernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
        {ω' | postCount (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω') = k}) =ᵐ[P]
      P[{ω' | postCount (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω') = k}.indicator fun _ => (1 : ℝ) |
        C.selectionSigma] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hle hER
  filter_upwards [hcondExp, hcondDistrib', hTailKernel', hkernel] with ω hce hdist htail hkern
  have htailLawω :
      (K (C.firstReportTime ω)).real
          {r | postCount (C.firstReportTime ω, C.startTime ω) r = k} = ν.real {k} :=
    htailLaw (C.firstReportTime ω) (C.startTime ω) k (C.firstReport_le_start ω)
  have hintegral :
      (∫ r, f (X ω, r) ∂ProbabilityTheory.condDistrib R X P (X ω)) = ν.real {k} := by
    rw [hdist]
    change ∫ r, f (X ω, r) ∂
      ProbabilityTheory.condDistrib R C.firstReportTime P (C.firstReportTime ω) = ν.real {k}
    rw [htail]
    let Eω : Set Tail := {r | postCount (C.firstReportTime ω, C.startTime ω) r = k}
    have hEω : MeasurableSet Eω := by
      simpa only [Eω, Set.preimage_setOf_eq] using
        (hpostCount (measurableSet_singleton k)).preimage
          (measurable_const.prodMk measurable_id)
    have hfeq : (fun r : Tail => f (X ω, r)) = Eω.indicator (fun _ => (1 : ℝ)) := by
      funext r
      simp only [f, E, Eω, X, Set.indicator_apply, Set.mem_setOf_eq]
    rw [hfeq, integral_indicator hEω, setIntegral_const, smul_eq_mul, mul_one]
    simpa only [Eω] using htailLawω
  have hfun :
      (fun a : Ω => f (X a, R a)) =
        {a | postCount (C.firstReportTime a, C.startTime a)
          (C.postFirstReportTail a) = k}.indicator fun _ => (1 : ℝ) := by
    funext a
    simp only [f, E, X, R, Set.indicator_apply, Set.mem_setOf_eq]
  change (ProbabilityTheory.condExpKernel P
      (MeasurableSpace.comap X inferInstance) ω).real
      {ω' | postCount (C.firstReportTime ω', C.startTime ω')
        (C.postFirstReportTail ω') = k} = ν.real {k}
  calc
    (ProbabilityTheory.condExpKernel P (MeasurableSpace.comap X inferInstance) ω).real
        {ω' | postCount (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω') = k} =
        P[{ω' | postCount (C.firstReportTime ω', C.startTime ω')
          (C.postFirstReportTail ω') = k}.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap X inferInstance] ω := hkern
    _ = P[fun a => f (X a, R a) | MeasurableSpace.comap X inferInstance] ω := by
      rw [hfun]
    _ = ∫ r, f (X ω, r) ∂ProbabilityTheory.condDistrib R X P (X ω) := hce
    _ = ν.real {k} := hintegral

/--
The same corrected Lemma-2 atom law after forgetting the selected start and
conditioning only on `T₁`.  This uses the conditional-expectation tower
property; it is still limited to the full-tail kernel model above, rather
than the paper's later history- and end-time-dependent likelihood theorem.
-/
theorem conditional_postTailCount_atom_given_firstReport_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (postCount : (ℝ≥0 × ℝ≥0) → Tail → ℕ)
    (hpostCount : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postCount p.1 p.2)
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (htailLaw : ∀ (t s : ℝ≥0) (k : ℕ), t ≤ s →
      (K t).real {r | postCount (t, s) r = k} = ν.real {k})
    (k : ℕ) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | postCount (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω') = k} =
        ν.real {k} := by
  let X : Ω → ℝ≥0 × ℝ≥0 := fun ω => (C.firstReportTime ω, C.startTime ω)
  let R : Ω → Tail := C.postFirstReportTail
  let Y : Ω → ℕ := fun ω => postCount (X ω) (R ω)
  let A : Set Ω := {ω | Y ω = k}
  have hX : Measurable X := C.selection_measurable
  have hR : Measurable R := C.postFirstReportTail_measurable
  have hY : Measurable Y := hpostCount.comp (hX.prodMk hR)
  have hA : MeasurableSet A := by
    simpa only [A, Set.preimage_setOf_eq] using hY (measurableSet_singleton k)
  have hfirstle_selection :
      MeasurableSpace.comap C.firstReportTime inferInstance ≤ C.selectionSigma := by
    have hpair : Measurable[C.selectionSigma]
        (fun ω => (C.firstReportTime ω, C.startTime ω)) := comap_measurable _
    exact (measurable_fst.comp hpair).comap_le
  have hselectionle : C.selectionSigma ≤ ‹MeasurableSpace Ω› := by
    simpa only [Theorem2ConditionOneSelection.selectionSigma] using hX.comap_le
  have hfirstle : MeasurableSpace.comap C.firstReportTime inferInstance ≤
      ‹MeasurableSpace Ω› := C.firstReportTime_measurable.comap_le
  letI : IsFiniteMeasure (P.trim hselectionle) := MeasureTheory.isFiniteMeasure_trim hselectionle
  have hselectionKernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real A) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hselectionle hA
  have hselectionAtom : ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real A = ν.real {k} := by
    simpa only [X, R, Y, A] using
      C.conditional_postTailCount_atom_of_tailKernel postCount hpostCount K hTailKernel
        ν htailLaw k
  have hselectionCondExp :
      P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] =ᵐ[P]
        fun _ => ν.real {k} :=
    hselectionKernel.symm.trans hselectionAtom
  have htower :
      P[P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] |
        MeasurableSpace.comap C.firstReportTime inferInstance] =ᵐ[P]
        P[A.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap C.firstReportTime inferInstance] :=
    condExp_condExp_of_le hfirstle_selection hselectionle
  have hfirstCondExp :
      P[A.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap C.firstReportTime inferInstance] =ᵐ[P]
        fun _ => ν.real {k} := by
    calc
      P[A.indicator fun _ => (1 : ℝ) |
          MeasurableSpace.comap C.firstReportTime inferInstance] =ᵐ[P]
          P[P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] |
            MeasurableSpace.comap C.firstReportTime inferInstance] :=
        htower.symm
      _ =ᵐ[P] P[fun _ : Ω => ν.real {k} |
          MeasurableSpace.comap C.firstReportTime inferInstance] :=
        condExp_congr_ae hselectionCondExp
      _ =ᵐ[P] fun _ => ν.real {k} := by
        rw [condExp_const hfirstle]
  have hfirstKernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real A) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) |
        MeasurableSpace.comap C.firstReportTime inferInstance] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hfirstle hA
  simpa only [X, R, Y, A] using hfirstKernel.trans hfirstCondExp

/--
Corrected Lemma-2 count-law bridge for an actual post-selected-start count.
The pathwise representation hypothesis ties the caller's `Tail` to that
count; the theorem does not assert the paper's remaining history-level or
end-time likelihood claims.
-/
theorem conditional_postStartCount_hasLaw_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (u : ℝ≥0)
    (postCount : (ℝ≥0 × ℝ≥0) → Tail → ℕ)
    (hpostCount : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postCount p.1 p.2)
    (hrepresentation : ∀ ω,
      forwardPostStopIntervalCount H C.startTime u ω =
        postCount (C.firstReportTime ω, C.startTime ω)
          (C.postFirstReportTail ω))
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (htailLaw : ∀ (t s : ℝ≥0) (k : ℕ), t ≤ s →
      (K t).real {r | postCount (t, s) r = k} = ν.real {k}) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.HasLaw (forwardPostStopIntervalCount H C.startTime u) ν
        (ProbabilityTheory.condExpKernel P C.selectionSigma ω) := by
  let X : Ω → ℝ≥0 × ℝ≥0 := fun ω => (C.firstReportTime ω, C.startTime ω)
  let R : Ω → Tail := C.postFirstReportTail
  let Y : Ω → ℕ := forwardPostStopIntervalCount H C.startTime u
  have hX : Measurable X := C.selection_measurable
  have hR : Measurable R := C.postFirstReportTail_measurable
  have hY : Measurable Y := by
    have htail : Measurable (fun ω => postCount (X ω) (R ω)) :=
      hpostCount.comp (hX.prodMk hR)
    have hYeq : Y = fun ω => postCount (X ω) (R ω) := by
      funext ω
      exact hrepresentation ω
    rw [hYeq]
    exact htail
  have hatoms : ∀ᵐ ω ∂P, ∀ k : ℕ,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
        {ω' | Y ω' = k} = ν.real {k} := by
    rw [ae_all_iff]
    intro k
    filter_upwards [C.conditional_postTailCount_atom_of_tailKernel
      postCount hpostCount K hTailKernel ν htailLaw k] with ω hω
    simpa only [Y, hrepresentation] using hω
  filter_upwards [hatoms] with ω hω
  refine ⟨hY.aemeasurable, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro k
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply hY (measurableSet_singleton k)]
  exact hω k

/--
Paper-facing corrected Lemma-2 count law: under the explicit full-tail model,
the selected-start count has law `ν` even after conditioning only on the first
report.  This is a residual-tail result, not a substitute for the source's
full stopped-history calculation.
-/
theorem conditional_postStartCount_hasLaw_given_firstReport_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (u : ℝ≥0)
    (postCount : (ℝ≥0 × ℝ≥0) → Tail → ℕ)
    (hpostCount : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postCount p.1 p.2)
    (hrepresentation : ∀ ω,
      forwardPostStopIntervalCount H C.startTime u ω =
        postCount (C.firstReportTime ω, C.startTime ω)
          (C.postFirstReportTail ω))
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (htailLaw : ∀ (t s : ℝ≥0) (k : ℕ), t ≤ s →
      (K t).real {r | postCount (t, s) r = k} = ν.real {k}) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.HasLaw (forwardPostStopIntervalCount H C.startTime u) ν
        (ProbabilityTheory.condExpKernel P
          (MeasurableSpace.comap C.firstReportTime inferInstance) ω) := by
  let X : Ω → ℝ≥0 × ℝ≥0 := fun ω => (C.firstReportTime ω, C.startTime ω)
  let R : Ω → Tail := C.postFirstReportTail
  let Y : Ω → ℕ := forwardPostStopIntervalCount H C.startTime u
  have hX : Measurable X := C.selection_measurable
  have hR : Measurable R := C.postFirstReportTail_measurable
  have hY : Measurable Y := by
    have htail : Measurable (fun ω => postCount (X ω) (R ω)) :=
      hpostCount.comp (hX.prodMk hR)
    have hYeq : Y = fun ω => postCount (X ω) (R ω) := by
      funext ω
      exact hrepresentation ω
    rw [hYeq]
    exact htail
  have hatoms : ∀ᵐ ω ∂P, ∀ k : ℕ,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
        {ω' | Y ω' = k} = ν.real {k} := by
    rw [ae_all_iff]
    intro k
    filter_upwards [C.conditional_postTailCount_atom_given_firstReport_of_tailKernel
      postCount hpostCount K hTailKernel ν htailLaw k] with ω hω
    simpa only [Y, hrepresentation] using hω
  filter_upwards [hatoms] with ω hω
  refine ⟨hY.aemeasurable, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro k
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply hY (measurableSet_singleton k)]
  exact hω k

/-- The corrected Lemma-2 no-report probability under the full-tail model. -/
theorem conditional_postStartCount_zero_real_given_firstReport_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (u : ℝ≥0)
    (postCount : (ℝ≥0 × ℝ≥0) → Tail → ℕ)
    (hpostCount : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postCount p.1 p.2)
    (hrepresentation : ∀ ω,
      forwardPostStopIntervalCount H C.startTime u ω =
        postCount (C.firstReportTime ω, C.startTime ω)
          (C.postFirstReportTail ω))
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (htailLaw : ∀ (t s : ℝ≥0) (k : ℕ), t ≤ s →
      (K t).real {r | postCount (t, s) r = k} =
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam H.rate (u : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))).real {k}) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) := by
  filter_upwards [C.conditional_postStartCount_hasLaw_given_firstReport_of_tailKernel
    u postCount hpostCount hrepresentation K hTailKernel
    (ProbabilityTheory.poissonMeasure
      (rateExposureParam H.rate (u : ℝ)
        (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))) htailLaw] with ω hω
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)) hω 0 |>.trans
      (noArrivalProb_eq_countLikelihood_zero H.rate (u : ℝ)).symm

/-- The corrected Lemma-2 no-report conclusion in exponential-tail form. -/
theorem conditional_postStartCount_zero_real_eq_exponential_tail_given_firstReport_of_tailKernel
    {Tail : Type*} [MeasurableSpace Tail] [StandardBorelSpace Tail] [Nonempty Tail]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOneSelection Ω P Tail)
    (u : ℝ≥0)
    (postCount : (ℝ≥0 × ℝ≥0) → Tail → ℕ)
    (hpostCount : Measurable fun p : (ℝ≥0 × ℝ≥0) × Tail =>
      postCount p.1 p.2)
    (hrepresentation : ∀ ω,
      forwardPostStopIntervalCount H C.startTime u ω =
        postCount (C.firstReportTime ω, C.startTime ω)
          (C.postFirstReportTail ω))
    (K : Kernel ℝ≥0 Tail) [IsMarkovKernel K]
    (hTailKernel : ProbabilityTheory.condDistrib C.postFirstReportTail
      C.firstReportTime P =ᵐ[P.map C.firstReportTime] K)
    (htailLaw : ∀ (t s : ℝ≥0) (k : ℕ), t ≤ s →
      (K t).real {r | postCount (t, s) r = k} =
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam H.rate (u : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))).real {k}) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal := by
  filter_upwards [C.conditional_postStartCount_zero_real_given_firstReport_of_tailKernel
    u postCount hpostCount hrepresentation K hTailKernel htailLaw] with ω hω
  rw [hω]
  exact noArrivalProb_eq_exponential_tail H.rate H.rate_pos
    (NNReal.coe_nonneg u)

end Theorem2ConditionOneSelection

/--
Operational post-start tail factorization for Lemma 2.  This is a certificate
because its atomwise equation is not merely the paper's Condition 1: deriving
it also needs a post-first-report Poisson path model and a proof that the
random selected shift preserves each deterministic increment law.

The conditioning sigma-algebra is `σ(T₁, S)`, the stronger intermediate
conditioning used inside the source's Lemma 2 calculation.  The displayed
Lemma 2 conclusion conditions only on `σ(T₁)` and is derived below.  Neither
form stands in for the full stopped history used later in Appendix Theorem 2.
-/
structure Theorem2ConditionOnePostStartTailFactorizationCertificate
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) where
  firstReportTime : Ω → ℝ≥0
  startTime : Ω → ℝ≥0
  firstReportTime_measurable : Measurable firstReportTime
  startTime_measurable : Measurable startTime
  firstReport_le_start : ∀ ω, firstReportTime ω ≤ startTime ω
  firstReportTime_is_first_count_arrival : ∀ t : ℝ≥0,
    {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ H.count t ω}
  postStartCount_measurable : ∀ u : ℝ≥0,
    Measurable (forwardPostStopIntervalCount H startTime u)
  postStartCount_atom_factorization : ∀ (u : ℝ≥0) (k : ℕ) (A : Set Ω),
    MeasurableSet[
      MeasurableSpace.comap (fun ω => (firstReportTime ω, startTime ω)) inferInstance] A →
      P.real (A ∩ {ω | forwardPostStopIntervalCount H startTime u ω = k}) =
        P.real A *
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam H.rate (u : ℝ)
              (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))).real {k}

namespace Theorem2ConditionOnePostStartTailFactorizationCertificate

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}

/-- The source-relevant conditioning sigma-algebra `σ(T₁, S)`. -/
abbrev selectionSigma
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (C.firstReportTime ω, C.startTime ω)) inferInstance

/-- The sigma-algebra generated by the first report alone. -/
abbrev firstReportSigma
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap C.firstReportTime inferInstance

theorem selection_measurable
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H) :
    Measurable fun ω => (C.firstReportTime ω, C.startTime ω) :=
  C.firstReportTime_measurable.prodMk C.startTime_measurable

theorem firstReportSigma_le_selectionSigma
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H) :
    C.firstReportSigma ≤ C.selectionSigma := by
  have hpair : Measurable[C.selectionSigma]
      (fun ω => (C.firstReportTime ω, C.startTime ω)) :=
    comap_measurable _
  exact (measurable_fst.comp hpair).comap_le

/--
Atomwise regular conditional law of the random post-start count, given
`σ(T₁, S)`.  This is the formal disintegration consequence of the
certificate's factorization field.
-/
theorem conditional_postStartCount_atom
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) (k : ℕ) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = k} =
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam H.rate (u : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))).real {k} := by
  let Y : Ω → ℕ := forwardPostStopIntervalCount H C.startTime u
  let A : Set Ω := {ω | Y ω = k}
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (rateExposureParam H.rate (u : ℝ)
      (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))
  have hY : Measurable Y := by
    simpa only [Y] using C.postStartCount_measurable u
  have hA : MeasurableSet A := by
    simpa only [A, Set.preimage_setOf_eq] using hY (measurableSet_singleton k)
  have hle : C.selectionSigma ≤ ‹MeasurableSpace Ω› := by
    simpa only [selectionSigma] using C.selection_measurable.comap_le
  letI : IsFiniteMeasure (P.trim hle) := MeasureTheory.isFiniteMeasure_trim hle
  have hcond : (fun _ : Ω => ν.real {k}) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] := by
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hle
      ((integrable_const (1 : ℝ)).indicator hA)
    · intro s hs htop
      exact (integrable_const (ν.real {k})).integrableOn
    · intro s hs htop
      rw [setIntegral_const, integral_indicator hA, setIntegral_const,
        MeasureTheory.measureReal_restrict_apply hA]
      simpa only [smul_eq_mul, mul_one, Set.inter_comm, Y, A, ν] using
        (C.postStartCount_atom_factorization u k s hs).symm
    · exact stronglyMeasurable_const.aestronglyMeasurable
  have hkernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real A) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) | C.selectionSigma] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hle hA
  simpa only [Y, A, ν] using hkernel.trans hcond.symm

/--
The same atomwise law after forgetting the selected start and conditioning
only on the first report.  This follows because `σ(T₁) ⊆ σ(T₁, S)`, so the
factorization certificate applies to every first-report-measurable event.
-/
theorem conditional_postStartCount_atom_given_firstReport
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) (k : ℕ) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.firstReportSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = k} =
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam H.rate (u : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))).real {k} := by
  let Y : Ω → ℕ := forwardPostStopIntervalCount H C.startTime u
  let A : Set Ω := {ω | Y ω = k}
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (rateExposureParam H.rate (u : ℝ)
      (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))
  have hY : Measurable Y := by
    simpa only [Y] using C.postStartCount_measurable u
  have hA : MeasurableSet A := by
    simpa only [A, Set.preimage_setOf_eq] using hY (measurableSet_singleton k)
  have hle : C.firstReportSigma ≤ ‹MeasurableSpace Ω› := by
    simpa only [firstReportSigma] using C.firstReportTime_measurable.comap_le
  letI : IsFiniteMeasure (P.trim hle) := MeasureTheory.isFiniteMeasure_trim hle
  have hcond : (fun _ : Ω => ν.real {k}) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) | C.firstReportSigma] := by
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hle
      ((integrable_const (1 : ℝ)).indicator hA)
    · intro s hs htop
      exact (integrable_const (ν.real {k})).integrableOn
    · intro s hs htop
      rw [setIntegral_const, integral_indicator hA, setIntegral_const,
        MeasureTheory.measureReal_restrict_apply hA]
      simpa only [smul_eq_mul, mul_one, Set.inter_comm, Y, A, ν] using
        (C.postStartCount_atom_factorization u k s
          (C.firstReportSigma_le_selectionSigma s hs)).symm
    · exact stronglyMeasurable_const.aestronglyMeasurable
  have hkernel : (fun ω =>
      (ProbabilityTheory.condExpKernel P C.firstReportSigma ω).real A) =ᵐ[P]
      P[A.indicator fun _ => (1 : ℝ) | C.firstReportSigma] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hle hA
  simpa only [Y, A, ν] using hkernel.trans hcond.symm

/--
Regular conditional Poisson law of a post-start count, given `σ(T₁, S)`.
This is the count-law version of the paper's Lemma 2 tail step.
-/
theorem conditional_postStartCount_hasLaw_poisson
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.HasLaw
        (forwardPostStopIntervalCount H C.startTime u)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam H.rate (u : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u))))
        (ProbabilityTheory.condExpKernel P C.selectionSigma ω) := by
  let Y : Ω → ℕ := forwardPostStopIntervalCount H C.startTime u
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (rateExposureParam H.rate (u : ℝ)
      (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)))
  have hY : Measurable Y := by
    simpa only [Y] using C.postStartCount_measurable u
  have hatoms : ∀ᵐ ω ∂P, ∀ k : ℕ,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | Y ω' = k} = ν.real {k} := by
    rw [ae_all_iff]
    intro k
    simpa only [Y, ν] using C.conditional_postStartCount_atom u k
  filter_upwards [hatoms] with ω hω
  refine ⟨hY.aemeasurable, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro k
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply hY (measurableSet_singleton k)]
  exact hω k

/-- Conditional no-report probability after the selected start in Lemma 2. -/
theorem conditional_postStartCount_zero_real
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) := by
  filter_upwards [C.conditional_postStartCount_hasLaw_poisson u] with ω hω
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)) hω 0 |>.trans
      (noArrivalProb_eq_countLikelihood_zero H.rate (u : ℝ)).symm

/-- The Lemma-2 no-report conclusion as an exponential waiting-time tail. -/
theorem conditional_postStartCount_zero_real_eq_exponential_tail
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal := by
  filter_upwards [C.conditional_postStartCount_zero_real u] with ω hω
  rw [hω]
  exact noArrivalProb_eq_exponential_tail H.rate H.rate_pos
    (NNReal.coe_nonneg u)

/--
The source's displayed Lemma 2 no-report conclusion, conditioning only on the
first report rather than also on the selected start.
-/
theorem conditional_postStartCount_zero_real_given_firstReport
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.firstReportSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) := by
  filter_upwards [C.conditional_postStartCount_atom_given_firstReport u 0]
    with ω hω
  exact hω.trans <|
    (countLikelihood_eq_poissonMeasure_real_singleton
      (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg u)) 0).symm.trans
      (noArrivalProb_eq_countLikelihood_zero H.rate (u : ℝ)).symm

/-- The source's displayed Lemma 2 conclusion in exponential-tail form. -/
theorem conditional_postStartCount_zero_real_eq_exponential_tail_given_firstReport
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.firstReportSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal := by
  filter_upwards [C.conditional_postStartCount_zero_real_given_firstReport u]
    with ω hω
  rw [hω]
  exact noArrivalProb_eq_exponential_tail H.rate H.rate_pos
    (NNReal.coe_nonneg u)

end Theorem2ConditionOnePostStartTailFactorizationCertificate

/--
Intermediate selected-start form of the Lemma 2 bridge.  It conditions on
`σ(T₁, S)`, not an arbitrary stopped filtration; the source's displayed
first-report-only form follows below.
-/
theorem lemma2_conditional_no_report_of_condition_one_tail_factorization
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) :=
  C.conditional_postStartCount_zero_real u

/-- The same selected-start bridge in exponential-tail form. -/
theorem lemma2_conditional_no_report_exponential_tail_of_condition_one_tail_factorization
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.selectionSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal :=
  C.conditional_postStartCount_zero_real_eq_exponential_tail u

/--
Paper-facing form of Lemma 2: the no-report tail conditional only on the
first report.  This is obtained from the same explicit tail-factorization
certificate, not from a generic stopping-time assertion.
-/
theorem lemma2_conditional_no_report_given_firstReport_of_condition_one_tail_factorization
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.firstReportSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        noArrivalProb H.rate (u : ℝ) :=
  C.conditional_postStartCount_zero_real_given_firstReport u

/-- The paper-facing first-report-only Lemma 2 bridge in exponential-tail form. -/
theorem
    lemma2_conditional_no_report_exponential_tail_given_firstReport_of_condition_one_tail_factorization
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (C : Theorem2ConditionOnePostStartTailFactorizationCertificate Ω P H)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P C.firstReportSigma ω).real
          {ω' | forwardPostStopIntervalCount H C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal :=
  C.conditional_postStartCount_zero_real_eq_exponential_tail_given_firstReport u

end
end LBG24SpatialUnderreporting

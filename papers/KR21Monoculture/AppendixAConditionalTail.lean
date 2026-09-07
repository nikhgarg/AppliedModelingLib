import KR21Monoculture.AppendixASourceFormula
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

noncomputable section

/-!
# Appendix A conditional-tail factorization

This module supplies the Fubini step in the source display (A.1).  We split
the iid finite noise vector into the distinguished coordinate `0` and the
remaining coordinates.  The law is an actual finite iid product law, and the
right-hand side is a literal integral of the conditional tail probability;
there is no conditional-probability equality supplied as a premise.
-/

/-- The iid law of the non-distinguished source-noise coordinates. -/
noncomputable def sourceAppendixARestNoiseLaw (n : Nat) (mu : Measure Real) :
    Measure (Fin (n + 1) -> Real) :=
  Measure.pi (fun _ : Fin (n + 1) => mu)

/-- Reassemble the distinguished noise coordinate and its finite remainder
into the paper's canonical candidate carrier. -/
def sourceAppendixAProductNoise {n : Nat}
    (z : Prod (Fin (n + 1) -> Real) Real) : Candidate n -> Real :=
  fun c => Fin.cases z.2 (fun d => z.1 d) c

/-- The literal A.1 tail event after the non-distinguished coordinates have
been fixed. -/
def SourceAppendixAFirstTail {n : Nat}
    (value : Candidate n -> Real) (theta : Real)
    (rest : Fin (n + 1) -> Real) (epsilon : Real) : Prop :=
  forall d : Fin (n + 1),
    theta * (value (Fin.succ d) - value 0) + rest d < epsilon

/-- The tail event on the reassembled noise vector is exactly the fiber tail
predicate appearing in the A.1 expectation. -/
theorem sourceAppendixA_tailEvent_productNoise_iff_firstTail
    {n : Nat} (value : Candidate n -> Real) (theta : Real)
    (z : Prod (Fin (n + 1) -> Real) Real) :
    SourceAppendixATailEvent value (sourceAppendixAProductNoise z) theta 0 <->
      SourceAppendixAFirstTail value theta z.1 z.2 := by
  constructor
  · intro h d
    have hd : (Fin.succ d : Candidate n) ≠ 0 := Fin.succ_ne_zero d
    simpa [sourceAppendixAProductNoise] using h (Fin.succ d) hd
  · intro h d hd
    rcases Fin.eq_zero_or_eq_succ d with hzero | ⟨d', hd'⟩
    · exact False.elim (hd hzero)
    · subst d
      simpa [sourceAppendixAProductNoise] using h d'

private theorem sourceAppendixA_firstTail_measurableSet
    {n : Nat} (value : Candidate n -> Real) (theta : Real)
    (rest : Fin (n + 1) -> Real) :
    MeasurableSet {epsilon : Real |
      SourceAppendixAFirstTail value theta rest epsilon} := by
  have hset : {epsilon : Real |
      SourceAppendixAFirstTail value theta rest epsilon} =
      ⋂ d : Fin (n + 1),
        {epsilon : Real |
          theta * (value (Fin.succ d) - value 0) + rest d < epsilon} := by
    ext epsilon
    simp [SourceAppendixAFirstTail]
  rw [hset]
  exact MeasurableSet.iInter fun d =>
    measurableSet_lt measurable_const measurable_id

private theorem sourceAppendixA_firstTail_product_measurableSet
    {n : Nat} (value : Candidate n -> Real) (theta : Real) :
    MeasurableSet {z : Prod (Fin (n + 1) -> Real) Real |
      SourceAppendixAFirstTail value theta z.1 z.2} := by
  have hset : {z : Prod (Fin (n + 1) -> Real) Real |
      SourceAppendixAFirstTail value theta z.1 z.2} =
      ⋂ d : Fin (n + 1),
        {z : Prod (Fin (n + 1) -> Real) Real |
          theta * (value (Fin.succ d) - value 0) + z.1 d < z.2} := by
    ext z
    simp [SourceAppendixAFirstTail]
  rw [hset]
  exact MeasurableSet.iInter fun d =>
    measurableSet_lt
      (measurable_const.add ((measurable_pi_apply d).comp measurable_fst))
      measurable_snd

/--
The source A.1 conditional-tail formula on a finite iid product law.  The
left side is the paper's actual selected-top event.  The right side is the
expectation over all other iid noise coordinates of the probability that the
distinguished coordinate exceeds the displayed finite tail threshold.

The a.e. no-tie premise is explicit: the library's ranking operation has a
deterministic tie rule, whereas the source display uses strict inequalities.
-/
theorem sourceAppendixA_selectedTop_probability_eq_conditionalTail_integral
    {n : Nat} (mu : Measure Real) [IsProbabilityMeasure mu]
    (value : Candidate n -> Real) {theta : Real} (htheta : 0 < theta)
    (hnoTie : ∀ᵐ z ∂(sourceAppendixARestNoiseLaw n mu).prod mu,
      forall i j : Candidate n, i ≠ j ->
        value i + sourceAppendixAProductNoise z i / theta ≠
          value j + sourceAppendixAProductNoise z j / theta) :
    AppliedModelingLib.measureProb ((sourceAppendixARestNoiseLaw n mu).prod mu)
        (fun z => SourceAppendixATopEvent value
          (sourceAppendixAProductNoise z) theta 0) =
      ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb mu
          (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon)
        ∂sourceAppendixARestNoiseLaw n mu := by
  classical
  let restLaw : Measure (Fin (n + 1) -> Real) :=
    sourceAppendixARestNoiseLaw n mu
  letI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw, sourceAppendixARestNoiseLaw]
    infer_instance
  let tail : Set (Prod (Fin (n + 1) -> Real) Real) :=
    {z | SourceAppendixAFirstTail value theta z.1 z.2}
  have htail : MeasurableSet tail := by
    exact sourceAppendixA_firstTail_product_measurableSet value theta
  have htop_tail :
      AppliedModelingLib.measureProb (restLaw.prod mu)
          (fun z => SourceAppendixATopEvent value
            (sourceAppendixAProductNoise z) theta 0) =
        AppliedModelingLib.measureProb (restLaw.prod mu)
          (fun z => SourceAppendixAFirstTail value theta z.1 z.2) := by
    unfold AppliedModelingLib.measureProb
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hnoTie] with z hz
    exact propext
      ((source_appendixA_top_event_iff_tail_event_of_no_ties
        value (sourceAppendixAProductNoise z) htheta 0 hz).trans
        (sourceAppendixA_tailEvent_productNoise_iff_firstTail value theta z))
  have hintegrable :
      Integrable (tail.indicator (fun _ : Prod (Fin (n + 1) -> Real) Real =>
        (1 : Real))) (restLaw.prod mu) :=
    (integrable_const _).indicator htail
  have hfubini := integral_prod
    (f := tail.indicator (fun _ : Prod (Fin (n + 1) -> Real) Real =>
      (1 : Real))) hintegrable
  calc
    AppliedModelingLib.measureProb ((sourceAppendixARestNoiseLaw n mu).prod mu)
        (fun z => SourceAppendixATopEvent value
          (sourceAppendixAProductNoise z) theta 0) =
        AppliedModelingLib.measureProb (restLaw.prod mu)
          (fun z => SourceAppendixATopEvent value
            (sourceAppendixAProductNoise z) theta 0) := by
      rfl
    _ = AppliedModelingLib.measureProb (restLaw.prod mu)
          (fun z => SourceAppendixAFirstTail value theta z.1 z.2) :=
      htop_tail
    _ = (restLaw.prod mu).real tail := by
      rfl
    _ = ∫ z, tail.indicator (fun _ : Prod (Fin (n + 1) -> Real) Real =>
          (1 : Real)) z ∂restLaw.prod mu := by
      simpa using (integral_indicator_one htail).symm
    _ = ∫ rest : Fin (n + 1) -> Real,
        ∫ epsilon : Real,
          tail.indicator (fun _ : Prod (Fin (n + 1) -> Real) Real =>
            (1 : Real)) (rest, epsilon) ∂mu ∂restLaw := hfubini
    _ = ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb mu
          (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon)
        ∂restLaw := by
      apply integral_congr_ae
      filter_upwards with rest
      let fiber : Set Real :=
        {epsilon | SourceAppendixAFirstTail value theta rest epsilon}
      have hfiber : MeasurableSet fiber :=
        sourceAppendixA_firstTail_measurableSet value theta rest
      have hfiber_fun :
          (fun epsilon : Real =>
            tail.indicator (fun _ : Prod (Fin (n + 1) -> Real) Real =>
              (1 : Real)) (rest, epsilon)) =
            fiber.indicator (fun _ : Real => (1 : Real)) := by
        funext epsilon
        change (if SourceAppendixAFirstTail value theta rest epsilon then 1 else 0) =
          (if SourceAppendixAFirstTail value theta rest epsilon then 1 else 0)
        rfl
      rw [hfiber_fun]
      calc
        (∫ epsilon : Real, fiber.indicator (fun _ : Real => (1 : Real)) epsilon ∂mu) =
            mu.real fiber := by
          simpa using (integral_indicator_one hfiber)
        _ = AppliedModelingLib.measureProb mu
            (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon) := by
          rfl
    _ = ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb mu
          (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon)
        ∂sourceAppendixARestNoiseLaw n mu := by
      rfl

end

end KR21Monoculture

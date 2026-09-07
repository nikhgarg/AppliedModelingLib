import LBG24SpatialUnderreporting.CausalEndpointKernelSource
import LBG24SpatialUnderreporting.KernelCausalEndpointBridge

/-!
# Fixed-cap Palm likelihood bridge for LBG

This module proves a deliberately restricted Palm-likelihood bridge.  It
fixes the Palm tag at time zero and takes one deterministic absolute endpoint
cap `c` after that tag.  Every endpoint coordinate is derived from that same
`c` and the same post-tag gap block; no endpoint clock is resampled.

The kernel model requires a nonnegative remaining-time kernel on every
history, including histories that are already past the cap.  We therefore use
`max 0 (c - elapsed)` as a total off-path extension.  On a history with
nonnegative raw remaining time it agrees with the single absolute cap.  This
module is not a derivation from the archived Conditions 1--2 and must not be
cited as an Eq. (8) source-model closure.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

namespace FixedCapPalmBridge

/-- The elapsed time represented by an arrival-prefix history. -/
def prefixElapsed (n : ℕ) (history : Fin n -> ℝ) : ℝ :=
  match n with
  | 0 => 0
  | m + 1 => history (Fin.last m)

theorem measurable_prefixElapsed (n : ℕ) : Measurable (prefixElapsed n) := by
  cases n with
  | zero => exact measurable_const
  | succ n =>
    simpa [prefixElapsed] using
      (measurable_pi_apply (Fin.last n) :
        Measurable (fun h : Fin (n + 1) -> ℝ => h (Fin.last n)))

/-- The totalized remaining time for a single absolute cap `c` after the
Palm tag.  The `max` is only an off-accepted-path extension. -/
def remainingCap (c : ℝ) {n : ℕ} (history : Fin n -> ℝ) : ℝ :=
  max 0 (c - prefixElapsed n history)

theorem measurable_remainingCap (c : ℝ) (n : ℕ) :
    Measurable (remainingCap c (n := n)) := by
  exact measurable_const.max
    (measurable_const.sub (measurable_prefixElapsed n))

theorem remainingCap_nonnegative (c : ℝ) {n : ℕ}
    (history : Fin n -> ℝ) :
    0 <= remainingCap c history :=
  le_max_left _ _

/-- On a physically live prefix, the totalized clock is exactly the raw
remaining time to the one absolute cap. -/
theorem remainingCap_eq_raw_of_nonnegative
    (c : ℝ) {n : ℕ} (history : Fin n -> ℝ)
    (hremaining : 0 <= c - prefixElapsed n history) :
    remainingCap c history = c - prefixElapsed n history := by
  exact max_eq_right hremaining

/-- The off-path clamp is invisible at an accepted stage with a nonnegative
gap: acceptance forces the raw remaining time to be nonnegative. -/
theorem remainingCap_eq_raw_of_nonnegative_gap_and_accepted
    (c : ℝ) {n : ℕ} (history : Fin n -> ℝ) (gap : ℝ)
    (hgap : 0 <= gap) (haccepted : gap < remainingCap c history) :
    remainingCap c history = c - prefixElapsed n history := by
  apply remainingCap_eq_raw_of_nonnegative
  by_contra hremaining
  have hraw_negative : c - prefixElapsed n history < 0 := lt_of_not_ge hremaining
  rw [remainingCap, max_eq_left hraw_negative.le] at haccepted
  exact (not_lt_of_ge hgap) haccepted

noncomputable def endpointKernel {count : ℕ} (c : ℝ)
    (j : Fin (count + 1)) : Kernel (Fin j.1 -> ℝ) ℝ :=
  deterministicEndpointKernel (remainingCap c (n := j.1))
    (measurable_remainingCap c j.1)

private theorem measurable_dirac_Ioi {count : ℕ} (i : Fin count)
    (f : (Fin count -> ℝ) -> ℝ) (hf : Measurable f) :
    Measurable (fun gaps : Fin count -> ℝ =>
      Measure.dirac (f gaps) (Set.Ioi (gaps i))) := by
  have hset : MeasurableSet {gaps : Fin count -> ℝ | gaps i < f gaps} :=
    measurableSet_lt (measurable_pi_apply i) hf
  have hind : Measurable
      ({gaps : Fin count -> ℝ | gaps i < f gaps}.indicator
        (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hset
  convert hind using 1
  funext gaps
  simp [Set.indicator]

private theorem finiteKernelProduct_deterministic
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (n : ℕ) (f : Fin n -> alpha -> beta) (hf : forall i, Measurable (f i)) :
    finiteKernelProduct n (fun i => Kernel.deterministic (f i) (hf i)) =
      Kernel.deterministic (fun a i => f i a) (measurable_pi_iff.2 hf) := by
  induction n with
  | zero =>
    simp only [finiteKernelProduct]
    apply Kernel.deterministic_congr
    funext a
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [finiteKernelProduct]
    rw [ih (fun i => f i.castSucc) (fun i => hf i.castSucc)]
    rw [Kernel.deterministic_prod_deterministic]
    rw [Kernel.deterministic_map _
      (finSnocMeasurableEquiv (beta := beta) n).measurable]
    apply Kernel.deterministic_congr
    funext a
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp [finSnocMeasurableEquiv_apply]
    · intro j
      simp [finSnocMeasurableEquiv_apply]

private theorem compProd_deterministic_response_eq_map
    {alpha beta gamma delta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] [MeasurableSpace gamma]
    [MeasurableSpace delta] [MeasurableSingletonClass beta]
    [MeasurableSingletonClass gamma]
    (mu : Measure alpha) (nu : Measure delta) [SFinite mu] [SFinite nu]
    (f : alpha -> beta) (hf : Measurable f)
    (g : alpha -> gamma) (hg : Measurable g) :
    mu ⊗ₘ (Kernel.deterministic f hf ×ₖ
      (Kernel.deterministic g hg ×ₖ Kernel.const alpha nu)) =
      Measure.map (fun p : alpha × delta =>
        (p.1, (f p.1, (g p.1, p.2)))) (mu.prod nu) := by
  letI : IsMarkovKernel (Kernel.deterministic f hf) := by infer_instance
  letI : IsMarkovKernel (Kernel.deterministic g hg) := by infer_instance
  letI : IsSFiniteKernel (Kernel.const alpha nu) := by infer_instance
  have hmap : Measurable (fun p : alpha × delta =>
      (p.1, (f p.1, (g p.1, p.2)))) :=
    measurable_fst.prodMk
      ((hf.comp measurable_fst).prodMk
        ((hg.comp measurable_fst).prodMk measurable_snd))
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [Measure.map_apply hmap hs]
  rw [Measure.prod_apply (hmap hs)]
  apply lintegral_congr
  intro a
  rw [Kernel.prod_apply, Kernel.deterministic_apply]
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply]
  have hs' : MeasurableSet (Prod.mk a ⁻¹' s) :=
    hs.preimage (measurable_const.prodMk measurable_id)
  rw [Measure.prod_apply hs']
  rw [MeasureTheory.lintegral_dirac]
  have hs'' : MeasurableSet
      (Prod.mk (f a) ⁻¹' (Prod.mk a ⁻¹' s)) :=
    hs'.preimage (measurable_const.prodMk measurable_id)
  rw [Measure.prod_apply hs'']
  rw [MeasureTheory.lintegral_dirac]
  congr 1

/-- The atom-safe collapsed model induced by one deterministic absolute cap.
It is a restricted model, not a generic endpoint-policy constructor. -/
noncomputable def model (count : ℕ) (c : ℝ) (startWeight : ℝ≥0∞) :
    CollapsedFiniteStageEndpointKernelModel count where
  startWeight := startWeight
  endKernel := endpointKernel c
  endKernel_isMarkov := fun j =>
    deterministicEndpointKernel_isMarkov (remainingCap c (n := j.1))
      (measurable_remainingCap c j.1)
  endKernel_nonnegative_support := by
    intro j history
    rw [show endpointKernel c j =
      deterministicEndpointKernel (remainingCap c (n := j.1))
        (measurable_remainingCap c j.1) by rfl]
    rw [deterministicEndpointKernel_apply]
    simp [not_lt_of_ge (remainingCap_nonnegative c history)]
  stageSurvival_measurable := by
    intro i
    change Measurable (fun gaps : Fin count -> ℝ =>
      Measure.dirac (remainingCap c (finiteArrivalPrefix gaps i.castSucc))
        (Set.Ioi (gaps i)))
    exact measurable_dirac_Ioi i _
      ((measurable_remainingCap c i.castSucc.1).comp
        (measurable_kernelFiniteArrivalPrefix i.castSucc))

def stageClock {count : ℕ} (c : ℝ) (i : Fin count)
    (gaps : Fin count -> ℝ) : ℝ :=
  remainingCap c (finiteArrivalPrefix gaps i.castSucc)

theorem measurable_stageClock {count : ℕ} (c : ℝ) (i : Fin count) :
    Measurable (stageClock c i) :=
  (measurable_remainingCap c i.castSucc.1).comp
    (measurable_kernelFiniteArrivalPrefix i.castSucc)

def nonterminalClocks {count : ℕ} (c : ℝ)
    (gaps : Fin count -> ℝ) : Fin count -> ℝ :=
  fun i => stageClock c i gaps

theorem measurable_nonterminalClocks {count : ℕ} (c : ℝ) :
    Measurable (nonterminalClocks (count := count) c) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact measurable_stageClock c i

def terminalClock {count : ℕ} (c : ℝ)
    (gaps : Fin count -> ℝ) : ℝ :=
  remainingCap c (finiteArrivalPrefix gaps (Fin.last count))

theorem measurable_terminalClock {count : ℕ} (c : ℝ) :
    Measurable (terminalClock (count := count) c) :=
  (measurable_remainingCap c (Fin.last count).1).comp
    (measurable_kernelFiniteArrivalPrefix (Fin.last count))

theorem model_stage_comap_eq_deterministic
    {count : ℕ} (c : ℝ) (startWeight : ℝ≥0∞) (i : Fin count) :
    Kernel.comap ((model count c startWeight).endKernel i.castSucc)
      (fun gaps : Fin count -> ℝ => finiteArrivalPrefix gaps i.castSucc)
      (measurable_kernelFiniteArrivalPrefix i.castSucc) =
      Kernel.deterministic (stageClock c i) (measurable_stageClock c i) := by
  ext gaps s hs
  rw [Kernel.comap_apply]
  change (deterministicEndpointKernel (remainingCap c)
    (measurable_remainingCap c i.castSucc.1)
    (finiteArrivalPrefix gaps i.castSucc)) s = _
  rw [deterministicEndpointKernel_apply]
  rw [Kernel.deterministic_apply]
  rfl

theorem model_nonterminalEndpointKernel
    {count : ℕ} (c : ℝ) (startWeight : ℝ≥0∞) :
    (model count c startWeight).nonterminalEndpointKernel =
      Kernel.deterministic (nonterminalClocks c)
        (measurable_nonterminalClocks c) := by
  unfold CollapsedFiniteStageEndpointKernelModel.nonterminalEndpointKernel
  have hfun : (fun i : Fin count =>
      Kernel.comap ((model count c startWeight).endKernel i.castSucc)
        (fun gaps : Fin count -> ℝ => finiteArrivalPrefix gaps i.castSucc)
        (measurable_kernelFiniteArrivalPrefix i.castSucc)) =
      fun i => Kernel.deterministic (stageClock c i)
        (measurable_stageClock c i) := by
    funext i
    exact model_stage_comap_eq_deterministic c startWeight i
  rw [hfun]
  simpa [nonterminalClocks] using
    (finiteKernelProduct_deterministic count
      (fun i => stageClock c i) (fun i => measurable_stageClock c i))

theorem model_terminalEndpointKernel
    {count : ℕ} (c : ℝ) (startWeight : ℝ≥0∞) :
    (model count c startWeight).terminalEndpointKernel =
      Kernel.deterministic (terminalClock c) (measurable_terminalClock c) := by
  ext gaps s hs
  rw [CollapsedFiniteStageEndpointKernelModel.terminalEndpointKernel,
    Kernel.comap_apply]
  change (deterministicEndpointKernel (remainingCap c)
    (measurable_remainingCap c (Fin.last count).1)
    (finiteArrivalPrefix gaps (Fin.last count))) s = _
  rw [deterministicEndpointKernel_apply]
  rw [Kernel.deterministic_apply]
  rfl

/-- The full finite latent vector generated from one cap and one report-gap
block.  The endpoint coordinates are functions, not independent samples. -/
def responseLatent {count : ℕ} (c : ℝ) :
    (Fin count -> ℝ) × ℝ ->
      (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) :=
  fun p => (p.1, (nonterminalClocks c p.1, (terminalClock c p.1, p.2)))

theorem measurable_responseLatent {count : ℕ} (c : ℝ) :
    Measurable (responseLatent (count := count) c) :=
  measurable_fst.prodMk
    ((measurable_nonterminalClocks c).comp measurable_fst |>.prodMk
      (((measurable_terminalClock c).comp measurable_fst).prodMk
        measurable_snd))

theorem model_responseLaw
    {count : ℕ} (c : ℝ) (startWeight : ℝ≥0∞)
    (gapLaw : Measure (Fin count -> ℝ)) [SFinite gapLaw]
    {rate : ℝ} (rate_pos : 0 < rate) :
    gapLaw ⊗ₘ (model count c startWeight).responseKernel rate =
      Measure.map (responseLatent c) (gapLaw.prod (expMeasure rate)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  unfold CollapsedFiniteStageEndpointKernelModel.responseKernel
  rw [model_nonterminalEndpointKernel c startWeight]
  rw [model_terminalEndpointKernel c startWeight]
  exact compProd_deterministic_response_eq_map gapLaw (expMeasure rate)
    (nonterminalClocks c) (measurable_nonterminalClocks c)
    (terminalClock c) (measurable_terminalClock c)

/-- The latent vector from one fixed Palm tag and one fixed absolute cap. -/
def oneCapPalmLatent
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    {P : Measure Ω} {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (c : ℝ) :
    Ω -> (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) :=
  responseLatent c ∘ S.postTagGapTail

theorem measurable_oneCapPalmLatent
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    {P : Measure Ω} {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (c : ℝ) : Measurable (oneCapPalmLatent S c) :=
  (measurable_responseLatent c).comp S.postTagGapTail_measurable

theorem oneCapPalmLatent_law
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    {P : Measure Ω} {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (c : ℝ) :
    P.map (oneCapPalmLatent S c) =
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) ⊗ₘ
        (model count c S.startWeight).responseKernel rate := by
  letI : IsProbabilityMeasure P := S.isProbabilityMeasure
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure S.rate_pos
  letI : forall _ : Fin count, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure S.rate_pos
  letI : IsProbabilityMeasure
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) := by
    unfold CollapsedFiniteStageEndpointModel.iidGapLaw
    infer_instance
  calc
    P.map (oneCapPalmLatent S c) =
        Measure.map (responseLatent c) (P.map S.postTagGapTail) := by
      rw [Measure.map_map (measurable_responseLatent c)
        S.postTagGapTail_measurable]
      rfl
    _ = Measure.map (responseLatent c)
        ((CollapsedFiniteStageEndpointModel.iidGapLaw count rate).prod
          (expMeasure rate)) := by
      rw [S.postTagGapTail_law]
    _ = (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) ⊗ₘ
        (model count c S.startWeight).responseKernel rate := by
      exact (model_responseLaw c S.startWeight
        (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) S.rate_pos).symm

/-- Restrict the one-cap Palm latent vector to accepted races and project to
the displayed gaps plus the remaining terminal endpoint time.

This is a fixed-tag likelihood measure (`startWeight • ...`), not a
conditional observation law or a paper-level selected-start transport. -/
def oneCapPalmLikelihood
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    {P : Measure Ω} {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (c : ℝ) : Measure ((Fin count -> ℝ) × ℝ) :=
  S.startWeight •
    Measure.map
      (fun p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) =>
        (p.1, p.2.2.1))
      ((P.map (oneCapPalmLatent S c)).restrict
        (CollapsedFiniteStageEndpointKernelModel.acceptedGapResponseSet
          (count := count)))

/-- Algebraically, the fixed-tag one-cap Palm likelihood equals the atom-safe
collapsed likelihood.  This uses only the verified Palm iid-gap law and one
deterministic cap; it does not close the archived general causal-model
obligation. -/
theorem oneCapPalmLikelihood_eq_collapsedObservationLaw_algebraic
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    {P : Measure Ω} {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (c : ℝ) :
    oneCapPalmLikelihood S c =
      (model count c S.startWeight).collapsedObservationLaw rate := by
  letI : IsProbabilityMeasure P := S.isProbabilityMeasure
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure S.rate_pos
  letI : forall _ : Fin count, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure S.rate_pos
  letI : IsProbabilityMeasure
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) := by
    unfold CollapsedFiniteStageEndpointModel.iidGapLaw
    infer_instance
  unfold oneCapPalmLikelihood
  rw [oneCapPalmLatent_law S c]
  rw [CollapsedFiniteStageEndpointKernelModel.map_restrict_responseLaw_eq_compProd_acceptedTail
    (model count c S.startWeight)
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) S.rate_pos]
  exact (model count c S.startWeight).generatedObservationLaw_eq_collapsedObservationLaw
    S.rate_pos

/-- For a physical cap after the Palm tag, the one-cap Palm likelihood is the
atom-safe collapsed likelihood.  The totalized clock is coherent with the
single absolute cap at any accepted stage whose Poisson gap is nonnegative,
by `remainingCap_eq_raw_of_nonnegative_gap_and_accepted`; its clamp only
supplies values on past-cap histories. This does not supply the
selected-start, history, lifetime, or rate-family transport required for the
paper-level model. -/
theorem oneCapPalmLikelihood_eq_collapsedObservationLaw
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    {P : Measure Ω} {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (c : ℝ) (hc : 0 <= c) :
    oneCapPalmLikelihood S c =
      (model count c S.startWeight).collapsedObservationLaw rate := by
  rcases lt_or_eq_of_le hc with hpositive | hzero
  · exact oneCapPalmLikelihood_eq_collapsedObservationLaw_algebraic S c
  · subst c
    exact oneCapPalmLikelihood_eq_collapsedObservationLaw_algebraic S 0

/-- Direct specialization to the verified two-sided Poisson suspension at a
Palm tag.  `c_nonnegative` records the physical fixed-cap interpretation;
the measure identity itself is proved by the stronger algebraic theorem. -/
theorem poissonSuspension_oneCapPalmLikelihood_eq_collapsedObservationLaw
    (rate : ℝ) (rate_pos : 0 < rate) (count : ℕ)
    (startWeight : ℝ≥0∞) (c : ℝ) (c_nonnegative : 0 <= c) :
    oneCapPalmLikelihood
      (StationaryPalmTaggedArrivalSource.ofPoissonSuspension
        rate rate_pos count startWeight) c =
      (model count c startWeight).collapsedObservationLaw rate := by
  exact oneCapPalmLikelihood_eq_collapsedObservationLaw
    (StationaryPalmTaggedArrivalSource.ofPoissonSuspension
      rate rate_pos count startWeight) c c_nonnegative

end FixedCapPalmBridge

end

end LBG24SpatialUnderreporting

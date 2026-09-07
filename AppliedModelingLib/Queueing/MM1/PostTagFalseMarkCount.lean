import AppliedModelingLib.Foundations.Probability.PoissonSuspensionFlow
import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning
import AppliedModelingLib.Queueing.MM1.Marked.Uniformization
import AppliedModelingLib.Queueing.RenewalFCFS

/-!
# Post-tag false-mark counts on a timed embedded path

This module defines the potential-service count supplied by `false` marks on
an actual tagged gap/marked-path pair.  It deliberately proves only structural
facts (measurability, bounds, and monotonicity).  A Poisson thinning law,
independence from the pre-arrival queue, and a response-time identity require
additional marked-path arguments and are not asserted here.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

open PoissonProcess

/-- The literal finite iid mark PMF used by finite marked thinning is exactly
the finite product measure of the uniformization Bernoulli mark law.  This
bridges the trajectory-side `Measure.pi` finite-window laws to the
path-faithful finite-horizon sample API. -/
theorem uniformizationIidMarks_toMeasure_eq_pi
    (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure =
      Measure.pi (fun _ : Fin n =>
        (uniformizationArrivalMark p hp).toMeasure) := by
  apply Measure.ext_of_singleton
  intro marks
  have hsingleton : ({marks} : Set (Fin n → Bool)) =
      Set.univ.pi (fun i : Fin n => ({marks i} : Set Bool)) := by
    ext x
    constructor
    · intro hx
      subst x
      simp
    · intro hx
      apply funext
      intro i
      simpa using hx i (by simp)
  rw [PMF.toMeasure_apply_singleton (FiniteHorizonMarkedPoisson.iidMarks p hp n)
      marks (measurableSet_singleton _), hsingleton, Measure.pi_pi]
  simp [FiniteHorizonMarkedPoisson.iidMarks, uniformizationArrivalMark]

/-- Symmetric form of `uniformizationIidMarks_toMeasure_eq_pi`. -/
theorem pi_uniformizationIidMarks_toMeasure
    (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    Measure.pi (fun _ : Fin n =>
      (uniformizationArrivalMark p hp).toMeasure) =
      (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure :=
  (uniformizationIidMarks_toMeasure_eq_pi p hp n).symm

/-- The number of post-tag potential-service (`false`-mark) clock events in
the first `n` all-event slots after the tagged event. -/
def postTagFalseMarkPrefixCount (n : ℕ) : (ℤ → (ℕ × Bool)) → ℕ :=
  fun markedPath =>
    ((Finset.range n).filter fun j =>
      (markedPath (Int.ofNat (j + 1))).2 = false).card

/-- The literal finite marked-Poisson sample formed from the first `n`
post-tag all-event marks.  This is a deterministic encoding of the same
actual path prefix, not a newly sampled independent mark vector. -/
def postTagFalseMarkPrefixSample (n : ℕ)
    (markedPath : ℤ → (ℕ × Bool)) :
    FiniteHorizonMarkedPoisson.Sample :=
  ⟨n, fun i => (markedPath (Int.ofNat (i.1 + 1))).2⟩

/-- The actual false-mark prefix count is exactly the discarded count of its
literal finite marked sample. -/
theorem postTagFalseMarkPrefixCount_eq_discarded
    (n : ℕ) (markedPath : ℤ → (ℕ × Bool)) :
    postTagFalseMarkPrefixCount n markedPath =
      FiniteHorizonMarkedPoisson.discarded
        (postTagFalseMarkPrefixSample n markedPath) := by
  classical
  let f : Fin n → Bool := fun i => (markedPath (Int.ofNat (i.1 + 1))).2
  have hfalse :
      (Finset.range n).filter fun j =>
        (markedPath (Int.ofNat (j + 1))).2 = false =
      (Finset.univ.filter fun i : Fin n => f i = false).map Fin.valEmbedding := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hjrange, hjfalse⟩
      have hjlt : j < n := Finset.mem_range.mp hjrange
      refine Finset.mem_map.mpr ⟨⟨j, hjlt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [f] using hjfalse⟩
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      rcases Finset.mem_filter.mp hi with ⟨_, hifalse⟩
      subst j
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, ?_⟩
      simpa [f] using hifalse
  have hnot :
      (Finset.univ.filter fun i : Fin n => f i = false) =
      Finset.univ.filter fun i : Fin n => ¬ f i = true := by
    ext i
    simp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin n => f i = true)
  have hcard :
      (Finset.univ.filter fun i : Fin n => f i = true).card +
        (Finset.univ.filter fun i : Fin n => f i = false).card = n := by
    rw [hnot]
    simpa using hpartition
  rw [postTagFalseMarkPrefixCount, hfalse]
  change ((Finset.univ.filter fun i : Fin n => f i = false).map Fin.valEmbedding).card =
    n - (Finset.univ.filter fun i : Fin n => f i = true).card
  rw [Finset.card_map]
  omega

/-- The actual post-tag potential-service count on a tagged gap/marked-path
pair.  The `j + 1` index intentionally excludes the tag at embedded index
zero. -/
def postTagFalseMarkCount (t : ℝ) :
    ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ :=
  fun z =>
    postTagFalseMarkPrefixCount
      (canonicalRenewalCount t (suspensionFuturePath z.1)) z.2

/-- The literal finite marked sample over the actual all-event horizon at
time `t`.  Its length is the actual renewal-clock count, and its marks are
the corresponding actual post-tag marks. -/
def postTagFalseMarkHorizonSample (t : ℝ) :
    ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → FiniteHorizonMarkedPoisson.Sample :=
  fun z => postTagFalseMarkPrefixSample
    (canonicalRenewalCount t (suspensionFuturePath z.1)) z.2

/-- The actual finite horizon sample is measurable: every one of its
countably many sample atoms is specified by a renewal-count atom and finitely
many post-tag mark-coordinate atoms. -/
theorem measurable_postTagFalseMarkHorizonSample (t : ℝ) :
    Measurable (postTagFalseMarkHorizonSample t) := by
  classical
  let N : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := fun z =>
    canonicalRenewalCount t (suspensionFuturePath z.1)
  have hN : Measurable N :=
    (measurable_canonicalRenewalCount t).comp
      (measurable_suspensionFuturePath.comp measurable_fst)
  refine measurable_to_countable' ?_
  rintro ⟨n, marks⟩
  have hpreimage : postTagFalseMarkHorizonSample t ⁻¹' ({⟨n, marks⟩} : Set _) =
      (N ⁻¹' ({n} : Set ℕ)) ∩
        ⋂ i : Fin n, {z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) |
          (z.2 (Int.ofNat (i.1 + 1))).2 = marks i} := by
    ext z
    simp [postTagFalseMarkHorizonSample, postTagFalseMarkPrefixSample, N]
    intro hn
    subst n
    constructor
    · intro h i
      exact congr_fun (eq_of_heq h) i
    · intro h
      exact heq_of_eq (funext h)
  rw [hpreimage]
  apply (hN (measurableSet_singleton _)).inter
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq.preimage
    (measurable_snd.comp
      ((measurable_pi_apply (Int.ofNat (i.1 + 1))).comp measurable_snd))

/-- If, for every deterministic prefix length, the actual all-event clock
count and the matching actual post-tag mark prefix have their Poisson-times-iid
law, then the literal random-length horizon sample has the finite marked
Poisson law.  This is the countable atomwise step that permits a random clock
horizon without replacing the path marks by a synthetic vector. -/
theorem postTagFalseMarkHorizonSample_hasLaw_of_count_prefix_hasLaw
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))}
    (t : ℝ) (mean p : ℝ≥0) (hp : p ≤ 1)
    (hprefix : ∀ n : ℕ, HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (canonicalRenewalCount t (suspensionFuturePath z.1),
          fun i : Fin n => (z.2 (Int.ofNat (i.1 + 1))).2))
      ((poissonMeasure mean).prod
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure) P) :
    HasLaw (postTagFalseMarkHorizonSample t)
      (FiniteHorizonMarkedPoisson.jointPMF mean p hp).toMeasure P := by
  refine ⟨(measurable_postTagFalseMarkHorizonSample t).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨n, marks⟩
  let N : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := fun z =>
    canonicalRenewalCount t (suspensionFuturePath z.1)
  let markPrefix : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → (Fin n → Bool) :=
    fun z i => (z.2 (Int.ofNat (i.1 + 1))).2
  have hN : Measurable N :=
    (measurable_canonicalRenewalCount t).comp
      (measurable_suspensionFuturePath.comp measurable_fst)
  have hprefix_meas : Measurable markPrefix := by
    apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp
      ((measurable_pi_apply (Int.ofNat (i.1 + 1))).comp measurable_snd)
  have hpref : HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      (N z, markPrefix z))
      ((poissonMeasure mean).prod
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure) P := by
    simpa [N, markPrefix] using hprefix n
  have hpreimage : postTagFalseMarkHorizonSample t ⁻¹' ({⟨n, marks⟩} : Set _) =
      (fun z => (N z, markPrefix z)) ⁻¹' ({(n, marks)} : Set _) := by
    ext z
    simp [postTagFalseMarkHorizonSample, postTagFalseMarkPrefixSample, N, markPrefix]
    intro hn
    subst n
    constructor
    · intro h
      exact eq_of_heq h
    · intro h
      exact heq_of_eq h
  rw [Measure.map_apply (measurable_postTagFalseMarkHorizonSample t)
    (measurableSet_singleton _), hpreimage,
    ← Measure.map_apply (hN.prodMk hprefix_meas) (measurableSet_singleton _),
    hpref.map_eq, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton (FiniteHorizonMarkedPoisson.jointPMF mean p hp)
      (FiniteHorizonMarkedPoisson.Sample.mk n marks) (measurableSet_singleton _),
    FiniteHorizonMarkedPoisson.jointPMF_apply]
  calc
    (poissonMeasure mean) {n} *
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure {marks} =
        ((poissonMeasure mean).toPMF).toMeasure {n} *
          (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure {marks} := by
            rw [Measure.toPMF_toMeasure]
    _ = (poissonMeasure mean).toPMF n *
          (FiniteHorizonMarkedPoisson.iidMarks p hp n) marks := by
            rw [PMF.toMeasure_apply_singleton (poissonMeasure mean).toPMF n
              (measurableSet_singleton _),
              PMF.toMeasure_apply_singleton (FiniteHorizonMarkedPoisson.iidMarks p hp n)
                marks (measurableSet_singleton _)]

/-- State-sensitive version of the random-horizon construction.  A product
law for the actual state, all-event count, and every matching finite mark
prefix gives a product law for that state and the actual finite horizon
sample.  This is the route by which finite marked thinning yields the needed
pre-arrival-state independence, rather than merely a count marginal. -/
theorem postTagFalseMarkHorizonSample_state_hasLaw_of_count_prefix_hasLaw
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))}
    (t : ℝ) (state : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ)
    (hstate : Measurable state)
    (stateLaw : Measure ℕ)
    (mean p : ℝ≥0) (hp : p ≤ 1)
    (hprefix : ∀ n : ℕ, HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (state z, (canonicalRenewalCount t (suspensionFuturePath z.1),
          fun i : Fin n => (z.2 (Int.ofNat (i.1 + 1))).2)))
      (stateLaw.prod ((poissonMeasure mean).prod
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)) P) :
    HasLaw (fun z => (state z, postTagFalseMarkHorizonSample t z))
      (stateLaw.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean p hp).toMeasure) P := by
  refine ⟨(hstate.prodMk (measurable_postTagFalseMarkHorizonSample t)).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨q, n, marks⟩
  let N : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := fun z =>
    canonicalRenewalCount t (suspensionFuturePath z.1)
  let markPrefix : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → (Fin n → Bool) :=
    fun z i => (z.2 (Int.ofNat (i.1 + 1))).2
  have hpref : HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      (state z, (N z, markPrefix z)))
      (stateLaw.prod ((poissonMeasure mean).prod
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)) P := by
    simpa [N, markPrefix] using hprefix n
  have hpreimage :
      (fun z => (state z, postTagFalseMarkHorizonSample t z)) ⁻¹'
        ({(q, FiniteHorizonMarkedPoisson.Sample.mk n marks)} : Set _) =
      (fun z => (state z, (N z, markPrefix z))) ⁻¹'
        ({(q, (n, marks))} : Set _) := by
    ext z
    simp [postTagFalseMarkHorizonSample, postTagFalseMarkPrefixSample, N, markPrefix]
    intro _ hcount
    subst n
    constructor
    · intro h
      exact eq_of_heq h
    · intro h
      exact heq_of_eq h
  rw [Measure.map_apply (hstate.prodMk (measurable_postTagFalseMarkHorizonSample t))
    (measurableSet_singleton _), hpreimage,
    ← Measure.map_apply_of_aemeasurable hpref.aemeasurable (measurableSet_singleton _),
    hpref.map_eq,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton (FiniteHorizonMarkedPoisson.jointPMF mean p hp)
      (FiniteHorizonMarkedPoisson.Sample.mk n marks) (measurableSet_singleton _),
    FiniteHorizonMarkedPoisson.jointPMF_apply]
  calc
    stateLaw {q} * ((poissonMeasure mean) {n} *
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure {marks}) =
        stateLaw {q} * (((poissonMeasure mean).toPMF).toMeasure {n} *
          (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure {marks}) := by
            rw [Measure.toPMF_toMeasure]
    _ = stateLaw {q} * ((poissonMeasure mean).toPMF n *
          (FiniteHorizonMarkedPoisson.iidMarks p hp n) marks) := by
            rw [PMF.toMeasure_apply_singleton (poissonMeasure mean).toPMF n
              (measurableSet_singleton _),
              PMF.toMeasure_apply_singleton (FiniteHorizonMarkedPoisson.iidMarks p hp n)
                marks (measurableSet_singleton _)]

/-- The actual potential-service count is the discarded count of the
corresponding literal finite horizon sample. -/
theorem postTagFalseMarkCount_eq_discarded_horizonSample
    (t : ℝ) (z : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) :
    postTagFalseMarkCount t z =
      FiniteHorizonMarkedPoisson.discarded
        (postTagFalseMarkHorizonSample t z) := by
  simpa [postTagFalseMarkCount, postTagFalseMarkHorizonSample] using
    (postTagFalseMarkPrefixCount_eq_discarded
      (canonicalRenewalCount t (suspensionFuturePath z.1)) z.2)

/-- The state-sensitive finite horizon law transports through literal
discarding to the corresponding state/false-mark-count product law. -/
theorem postTagFalseMarkCount_state_hasLaw_of_horizonSample_state_hasLaw
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))}
    (t : ℝ) (state : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ)
    (stateLaw : Measure ℕ) [SFinite stateLaw]
    (mean p : ℝ≥0) (hp : p ≤ 1)
    (hsample : HasLaw (fun z => (state z, postTagFalseMarkHorizonSample t z))
      (stateLaw.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean p hp).toMeasure) P) :
    HasLaw (fun z => (state z, postTagFalseMarkCount t z))
      (stateLaw.prod (poissonMeasure (mean * (1 - p)))) P := by
  let J : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF mean p hp).toMeasure
  let D : Measure ℕ := poissonMeasure (mean * (1 - p))
  have hdiscard : HasLaw FiniteHorizonMarkedPoisson.discarded D J := by
    simpa [J, D] using FiniteHorizonMarkedPoisson.discarded_hasLaw mean p hp
  have htransform : HasLaw
      (fun x : ℕ × FiniteHorizonMarkedPoisson.Sample =>
        (x.1, FiniteHorizonMarkedPoisson.discarded x.2))
      (stateLaw.prod D) (stateLaw.prod J) := by
    refine ⟨(measurable_fst.prodMk
      ((measurable_of_countable FiniteHorizonMarkedPoisson.discarded).comp
        measurable_snd)).aemeasurable, ?_⟩
    change Measure.map (fun x : ℕ × FiniteHorizonMarkedPoisson.Sample =>
      (x.1, FiniteHorizonMarkedPoisson.discarded x.2)) (stateLaw.prod J) =
        stateLaw.prod D
    calc
      Measure.map (fun x : ℕ × FiniteHorizonMarkedPoisson.Sample =>
          (x.1, FiniteHorizonMarkedPoisson.discarded x.2)) (stateLaw.prod J) =
          (stateLaw.map id).prod
            (J.map FiniteHorizonMarkedPoisson.discarded) := by
              simpa [Prod.map] using
                (Measure.map_prod_map stateLaw J measurable_id
                  (measurable_of_countable FiniteHorizonMarkedPoisson.discarded)).symm
      _ = stateLaw.prod D := by
        rw [Measure.map_id, hdiscard.map_eq]
  have hcomp := htransform.comp hsample
  have hfun : (fun z => (state z, postTagFalseMarkCount t z)) =
      (fun x : ℕ × FiniteHorizonMarkedPoisson.Sample =>
        (x.1, FiniteHorizonMarkedPoisson.discarded x.2)) ∘
        (fun z => (state z, postTagFalseMarkHorizonSample t z)) := by
    funext z
    exact Prod.ext rfl (postTagFalseMarkCount_eq_discarded_horizonSample t z)
  rw [hfun]
  exact hcomp

/-- A fixed finite false-mark prefix count is measurable. -/
theorem measurable_postTagFalseMarkPrefixCount (n : ℕ) :
    Measurable (postTagFalseMarkPrefixCount n) := by
  classical
  unfold postTagFalseMarkPrefixCount
  suffices hsum : Measurable (fun markedPath : ℤ → (ℕ × Bool) =>
      ∑ j ∈ Finset.range n,
        if (markedPath (Int.ofNat (j + 1))).2 = false then 1 else 0) by
    convert hsum using 1
    ext markedPath
    exact Finset.card_filter _ _
  apply (Finset.range n).measurable_sum
  intro j _
  apply Measurable.ite
  · exact (MeasurableSet.singleton false).preimage
      (measurable_snd.comp (measurable_pi_apply (Int.ofNat (j + 1))))
  · exact measurable_const
  · exact measurable_const

/-- The actual post-tag false-mark count is measurable at every fixed real
horizon. -/
theorem measurable_postTagFalseMarkCount (t : ℝ) :
    Measurable (postTagFalseMarkCount t) := by
  let N : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := fun z =>
    canonicalRenewalCount t (suspensionFuturePath z.1)
  have hN : Measurable N :=
    (measurable_canonicalRenewalCount t).comp
      (measurable_suspensionFuturePath.comp measurable_fst)
  refine measurable_to_nat ?_
  intro y
  have hfiber : postTagFalseMarkCount t ⁻¹' {postTagFalseMarkCount t y} =
      ⋃ n : ℕ, (N ⁻¹' ({n} : Set ℕ)) ∩
        ((fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
          postTagFalseMarkPrefixCount n z.2) ⁻¹'
          ({postTagFalseMarkCount t y} : Set ℕ)) := by
    ext z
    constructor
    · intro hz
      refine Set.mem_iUnion.2 ⟨N z, ?_, ?_⟩
      · rfl
      · simpa only [postTagFalseMarkCount, N] using hz
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨n, hn, hpref⟩
      change postTagFalseMarkPrefixCount (N z) z.2 = postTagFalseMarkCount t y
      rw [hn]
      exact hpref
  rw [hfiber]
  apply MeasurableSet.iUnion
  intro n
  exact (hN (MeasurableSet.singleton n)).inter
    (((measurable_postTagFalseMarkPrefixCount n).comp measurable_snd)
      (MeasurableSet.singleton (postTagFalseMarkCount t y)))

/-- A joint law for the actual finite horizon sample immediately yields the
Poisson law for the actual false-mark potential-service count.  The premise is
deliberately a law of the same path-derived sample, so this theorem introduces
no synthetic independent copy. -/
theorem postTagFalseMarkCount_hasLaw_of_horizonSample_hasLaw
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))}
    (t : ℝ) (mean p : ℝ≥0) (hp : p ≤ 1)
    (hsample : HasLaw (postTagFalseMarkHorizonSample t)
      (FiniteHorizonMarkedPoisson.jointPMF mean p hp).toMeasure P) :
    HasLaw (postTagFalseMarkCount t)
      (poissonMeasure (mean * (1 - p))) P := by
  have hdiscard := FiniteHorizonMarkedPoisson.discarded_hasLaw mean p hp
  have hcomp := hdiscard.comp hsample
  refine ⟨(measurable_postTagFalseMarkCount t).aemeasurable, ?_⟩
  have hfun : postTagFalseMarkCount t =
      FiniteHorizonMarkedPoisson.discarded ∘ postTagFalseMarkHorizonSample t := by
    funext z
    exact postTagFalseMarkCount_eq_discarded_horizonSample t z
  rw [hfun]
  exact hcomp.map_eq

private theorem uniformizedDiscardedMean_eq_serviceMean
    (arrivalRate serviceRate : ℝ≥0) (hservice_pos : 0 < serviceRate)
    (t : ℝ) (ht : 0 ≤ t) :
    NNReal.mk (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t)
      (mul_nonneg (by positivity) ht) *
        ((1 : ℝ≥0) - uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate)) =
      NNReal.mk ((serviceRate : ℝ) * t)
        (mul_nonneg (by positivity) ht) := by
  apply NNReal.eq
  change
    (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t) *
        (((1 : ℝ≥0) - uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ≥0) : ℝ) =
      (serviceRate : ℝ) * t
  calc
    (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t) *
        ((1 - uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ≥0) : ℝ) =
        (((arrivalRate + serviceRate : ℝ≥0) *
          ((1 : ℝ≥0) - uniformizedBirthProbability
            (mm1TrafficIntensityNN arrivalRate serviceRate)) : ℝ≥0) : ℝ) * t := by
          rw [NNReal.coe_mul]
          ring
    _ = (serviceRate : ℝ) * t := by
      rw [total_uniformized_rate_mul_potentialServiceProbability hservice_pos]

/-- At the physical M/M/1 uniformization parameters, a law for the literal
actual horizon sample yields the Poisson potential-service count with mean
`serviceRate * t`.  The finite sample-law premise remains the substantive
marked-Palm thinning obligation. -/
theorem postTagFalseMarkCount_hasLaw_poisson_serviceRate_of_uniformized_horizonSample_hasLaw
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))}
    (arrivalRate serviceRate : ℝ≥0) (hservice_pos : 0 < serviceRate)
    (t : ℝ) (ht : 0 ≤ t)
    (hsample : HasLaw (postTagFalseMarkHorizonSample t)
      (FiniteHorizonMarkedPoisson.jointPMF
        (NNReal.mk (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t)
          (mul_nonneg (by positivity) ht))
        (uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate))
        (uniformizedBirthProbability_le_one _)).toMeasure P) :
    HasLaw (postTagFalseMarkCount t)
      (poissonMeasure (NNReal.mk ((serviceRate : ℝ) * t)
        (mul_nonneg (by positivity) ht))) P := by
  simpa only [uniformizedDiscardedMean_eq_serviceMean arrivalRate serviceRate
    hservice_pos t ht] using
    (postTagFalseMarkCount_hasLaw_of_horizonSample_hasLaw t
      (NNReal.mk (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t)
        (mul_nonneg (by positivity) ht))
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate))
      (uniformizedBirthProbability_le_one _) hsample)

@[simp] theorem postTagFalseMarkPrefixCount_zero
    (markedPath : ℤ → (ℕ × Bool)) :
    postTagFalseMarkPrefixCount 0 markedPath = 0 := by
  simp [postTagFalseMarkPrefixCount]

/-- A false-mark prefix count never exceeds its number of all-event slots. -/
theorem postTagFalseMarkPrefixCount_le (n : ℕ)
    (markedPath : ℤ → (ℕ × Bool)) :
    postTagFalseMarkPrefixCount n markedPath ≤ n := by
  classical
  unfold postTagFalseMarkPrefixCount
  calc
    ((Finset.range n).filter fun j =>
      (markedPath (Int.ofNat (j + 1))).2 = false).card ≤
        (Finset.range n).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Finset.card_range n

/-- Extending an all-event prefix cannot decrease its false-mark count. -/
theorem postTagFalseMarkPrefixCount_monotone
    (markedPath : ℤ → (ℕ × Bool)) :
    Monotone (fun n => postTagFalseMarkPrefixCount n markedPath) := by
  classical
  intro n m hnm
  unfold postTagFalseMarkPrefixCount
  exact Finset.card_le_card <|
    Finset.filter_subset_filter _ (Finset.range_mono hnm)

/-- The next all-event slot adds exactly one iff it carries a false mark. -/
theorem postTagFalseMarkPrefixCount_succ
    (n : ℕ) (markedPath : ℤ → (ℕ × Bool)) :
    postTagFalseMarkPrefixCount (n + 1) markedPath =
      postTagFalseMarkPrefixCount n markedPath +
        if (markedPath (Int.ofNat (n + 1))).2 = false then 1 else 0 := by
  classical
  unfold postTagFalseMarkPrefixCount
  simp only [Finset.card_filter, Finset.sum_range_succ]

/-- The potential-service count is bounded by the total all-event renewal
count at the same horizon. -/
theorem postTagFalseMarkCount_le_allEventCount
    (t : ℝ) (z : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) :
    postTagFalseMarkCount t z ≤
      canonicalRenewalCount t (suspensionFuturePath z.1) := by
  exact postTagFalseMarkPrefixCount_le _ _

/-- If no post-tag all-event clock slot has completed, the false-mark count is
zero. -/
theorem postTagFalseMarkCount_eq_zero_of_renewalCount_eq_zero
    (t : ℝ) (z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)))
    (hzero : canonicalRenewalCount t (suspensionFuturePath z.1) = 0) :
    postTagFalseMarkCount t z = 0 := by
  simp [postTagFalseMarkCount, hzero]

/-- On a nonexplosive tagged gap path, the post-tag false-mark count is
monotone in real time. -/
theorem postTagFalseMarkCount_monotone_of_tendsto
    (gapPath : ℤ → ℝ) (markedPath : ℤ → (ℕ × Bool))
    (hdiv : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath gapPath)) atTop atTop) :
    Monotone (fun t => postTagFalseMarkCount t (gapPath, markedPath)) := by
  intro s t hst
  apply postTagFalseMarkPrefixCount_monotone
  exact canonicalRenewalCount_monotone_of_tendsto
    (suspensionFuturePath gapPath) hdiv hst

/-- If an actual post-tag false-mark count has an exponentially vanishing
queue-threshold tail at every deterministic horizon, then almost every path
eventually has enough `false` marks to clear that threshold.  The conclusion
is pathwise in the literal mark prefix; no synthetic infinite iid mark stream
is introduced. -/
theorem ae_exists_postTagFalseMarkPrefix_gt_of_exponential_count_tail
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))} [IsProbabilityMeasure P]
    (state : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ)
    (a : ℝ) (ha : 0 < a)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P.real {z | postTagFalseMarkCount t z ≤ state z} = Real.exp (-(a * t))) :
    ∀ᵐ z ∂P, ∃ n : ℕ, state z < postTagFalseMarkPrefixCount (n + 1) z.2 := by
  let bad : Set ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) :=
    {z | ¬ ∃ n : ℕ, state z < postTagFalseMarkPrefixCount (n + 1) z.2}
  have hbad_subset (t : ℝ) : bad ⊆ {z | postTagFalseMarkCount t z ≤ state z} := by
    intro z hz
    change ¬ ∃ n : ℕ, state z < postTagFalseMarkPrefixCount (n + 1) z.2 at hz
    change postTagFalseMarkPrefixCount
      (canonicalRenewalCount t (suspensionFuturePath z.1)) z.2 ≤ state z
    apply le_of_not_gt
    intro hgt
    generalize hN : canonicalRenewalCount t (suspensionFuturePath z.1) = N at hgt
    cases N with
    | zero =>
        exact (Nat.not_lt_zero (state z) (by
          simpa only [postTagFalseMarkPrefixCount_zero] using hgt)).elim
    | succ n =>
        apply hz
        refine ⟨n, ?_⟩
        simpa only [Nat.succ_eq_add_one] using hgt
  have hlin : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hdecay : Tendsto (fun n : ℕ => Real.exp (-(a * (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hbad_bound : ∀ n : ℕ,
      P.real bad ≤ Real.exp (-(a * (n : ℝ))) := by
    intro n
    calc
      P.real bad ≤ P.real {z | postTagFalseMarkCount (n : ℝ) z ≤ state z} :=
        MeasureTheory.measureReal_mono (hbad_subset (n : ℝ))
      _ = Real.exp (-(a * (n : ℝ))) := htail (n : ℝ) (by positivity)
  have hbad_real : P.real bad = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hdecay hbad_bound
    · exact MeasureTheory.measureReal_nonneg
  have hbad_measure : P bad = 0 := by
    have hzero_or_top : P bad = 0 ∨ P bad = ∞ :=
      (ENNReal.toReal_eq_zero_iff (P bad)).mp hbad_real
    rcases hzero_or_top with hzero | htop
    · exact hzero
    · exact (MeasureTheory.measure_ne_top P bad htop).elim
  rw [MeasureTheory.ae_iff]
  simpa only [bad] using hbad_measure

/-- The all-event epoch at which the `(q+1)`st post-tag false mark occurs;
the fallback on paths with finitely many false marks is zero. -/
noncomputable def postTagFalseMarkHitEpoch (q : ℕ)
    (markedPath : ℤ → (ℕ × Bool)) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) markedPath
    then Nat.find h else 0

theorem postTagFalseMarkHitEpoch_spec
    (q : ℕ) (markedPath : ℤ → (ℕ × Bool))
    (h : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) markedPath) :
    q < postTagFalseMarkPrefixCount
      (postTagFalseMarkHitEpoch q markedPath + 1) markedPath := by
  classical
  rw [postTagFalseMarkHitEpoch, dif_pos h]
  exact Nat.find_spec h

theorem postTagFalseMarkPrefixCount_le_queueLength_of_lt_hitEpoch
    (q : ℕ) (markedPath : ℤ → (ℕ × Bool))
    (h : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) markedPath)
    {n : ℕ} (hn : n < postTagFalseMarkHitEpoch q markedPath) :
    postTagFalseMarkPrefixCount (n + 1) markedPath ≤ q := by
  classical
  rw [postTagFalseMarkHitEpoch, dif_pos h] at hn
  exact Nat.le_of_not_gt (Nat.find_min h hn)

theorem postTagFalseMarkPrefixCount_le_queueLength_iff_le_hitEpoch
    (q : ℕ) (markedPath : ℤ → (ℕ × Bool))
    (h : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) markedPath)
    (n : ℕ) :
    postTagFalseMarkPrefixCount n markedPath ≤ q ↔
      n ≤ postTagFalseMarkHitEpoch q markedPath := by
  constructor
  · intro hcount
    by_contra hnot
    have hhit_lt : postTagFalseMarkHitEpoch q markedPath < n :=
      Nat.lt_of_not_ge hnot
    have hhit_succ_le : postTagFalseMarkHitEpoch q markedPath + 1 ≤ n := by
      omega
    have hhit : q < postTagFalseMarkPrefixCount
        (postTagFalseMarkHitEpoch q markedPath + 1) markedPath :=
      postTagFalseMarkHitEpoch_spec q markedPath h
    have hmono := postTagFalseMarkPrefixCount_monotone markedPath hhit_succ_le
    exact (not_lt_of_ge (hmono.trans hcount)) hhit
  · intro hn
    rcases lt_or_eq_of_le hn with hlt | rfl
    · cases n with
      | zero => simp [postTagFalseMarkPrefixCount_zero]
      | succ m =>
          have hm_lt : m < postTagFalseMarkHitEpoch q markedPath :=
            lt_trans (Nat.lt_succ_self _) hlt
          simpa [Nat.succ_eq_add_one] using
            (postTagFalseMarkPrefixCount_le_queueLength_of_lt_hitEpoch
              q markedPath h hm_lt)
    · cases hhit : postTagFalseMarkHitEpoch q markedPath with
      | zero => simp [postTagFalseMarkPrefixCount_zero]
      | succ m =>
          have hm_lt : m < postTagFalseMarkHitEpoch q markedPath := by
            rw [hhit]
            exact Nat.lt_succ_self _
          have hm := postTagFalseMarkPrefixCount_le_queueLength_of_lt_hitEpoch
            q markedPath h hm_lt
          simpa [hhit, Nat.succ_eq_add_one] using hm

/-- The time at which the `(q+1)`st post-tag false mark occurs, with the
zero fallback inherited from `postTagFalseMarkHitEpoch`. -/
noncomputable def postTagFalseMarkResponse (q : ℕ)
    (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) : ℝ :=
  arrivalTime (postTagFalseMarkHitEpoch q path.2)
    (suspensionFuturePath path.1)

/-- The literal false-mark response time when the target number of potential
services is the selected path's pre-arrival queue state. -/
noncomputable def postTagFalseMarkResponseFromState
    (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) : ℝ :=
  postTagFalseMarkResponse (path.2 0).1 path

/-- Time at which the jobs ahead of the tag have cleared under the false-mark
potential-service clock. -/
noncomputable def postTagFalseMarkBusyUntil (q : ℕ)
    (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) : ℝ :=
  match q with
  | 0 => 0
  | n + 1 => postTagFalseMarkResponse n path

/-- The tagged job's work requirement induced by the next false-mark response
epoch after the pre-tag busy-until time. -/
noncomputable def postTagFalseMarkTaggedServiceWork (serviceRate : ℝ) (q : ℕ)
    (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) : ℕ → ℝ :=
  fun n =>
    if n = 0 then
      serviceRate * (postTagFalseMarkResponse q path -
        postTagFalseMarkBusyUntil q path)
    else 0

/-- The false-mark tagged work is nonnegative when the service rate is
nonnegative and the next response epoch is after the pre-tag busy-until time. -/
theorem postTagFalseMarkTaggedServiceWork_nonneg
    {serviceRate : ℝ} {q : ℕ}
    {path : (ℤ → ℝ) × (ℤ → (ℕ × Bool))}
    (hserviceRate : 0 ≤ serviceRate)
    (hbusy_le_response :
      postTagFalseMarkBusyUntil q path ≤ postTagFalseMarkResponse q path) :
    ∀ n : ℕ, 0 ≤ postTagFalseMarkTaggedServiceWork serviceRate q path n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [postTagFalseMarkTaggedServiceWork,
      mul_nonneg hserviceRate (sub_nonneg.mpr hbusy_le_response)]
  · simp [postTagFalseMarkTaggedServiceWork, hn]

/--
With the false-mark-induced pre-tag busy-until time and tagged work, the
tag-only FCFS comparator response is exactly the false-mark response epoch.
-/
theorem postTagFalseMarkResponse_eq_fcfsTaggedResponse
    {serviceRate : ℝ} (hserviceRate : serviceRate ≠ 0) (q : ℕ)
    (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)))
    (hbusy_nonneg : 0 ≤ postTagFalseMarkBusyUntil q path) :
    responseTime tagOnlyArrival
      (fcfsDepartureFrom (postTagFalseMarkBusyUntil q path) tagOnlyArrival
        (postTagFalseMarkTaggedServiceWork serviceRate q path) serviceRate) 0 =
      postTagFalseMarkResponse q path := by
  simp [responseTime, fcfsDepartureFrom, tagOnlyArrival,
    postTagFalseMarkTaggedServiceWork, max_eq_right hbusy_nonneg]
  field_simp [hserviceRate]
  ring

/-- The first prefix epoch with enough false marks is monotone in the requested
number of false marks, provided the larger request is reachable. -/
theorem postTagFalseMarkHitEpoch_mono_of_le
    {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) (markedPath : ℤ → (ℕ × Bool))
    (hhit₂ : ∃ n : ℕ, q₂ < postTagFalseMarkPrefixCount (n + 1) markedPath) :
    postTagFalseMarkHitEpoch q₁ markedPath ≤
      postTagFalseMarkHitEpoch q₂ markedPath := by
  classical
  have hhit₁ : ∃ n : ℕ, q₁ < postTagFalseMarkPrefixCount (n + 1) markedPath := by
    rcases hhit₂ with ⟨n, hn⟩
    exact ⟨n, lt_of_le_of_lt hq hn⟩
  unfold postTagFalseMarkHitEpoch
  rw [dif_pos hhit₁, dif_pos hhit₂]
  have hprop : q₁ < postTagFalseMarkPrefixCount (Nat.find hhit₂ + 1) markedPath :=
    lt_of_le_of_lt hq (Nat.find_spec hhit₂)
  exact Nat.find_min' hhit₁ hprop

/--
The hit epoch for the next false mark is strictly later.  The prefix count can
increase by at most one at each all-event slot, so the first prefix containing
`q+2` false marks cannot be the first prefix containing `q+1` false marks.
-/
theorem postTagFalseMarkHitEpoch_lt_succ_of_hit
    (q : ℕ) (markedPath : ℤ → (ℕ × Bool))
    (hhit_succ : ∃ n : ℕ,
      q + 1 < postTagFalseMarkPrefixCount (n + 1) markedPath) :
    postTagFalseMarkHitEpoch q markedPath <
      postTagFalseMarkHitEpoch (q + 1) markedPath := by
  have hhit_q : ∃ n : ℕ,
      q < postTagFalseMarkPrefixCount (n + 1) markedPath := by
    rcases hhit_succ with ⟨n, hn⟩
    exact ⟨n, lt_trans (Nat.lt_succ_self q) hn⟩
  let m := postTagFalseMarkHitEpoch q markedPath
  have hcount_m_le :
      postTagFalseMarkPrefixCount m markedPath ≤ q := by
    have hiff :=
      postTagFalseMarkPrefixCount_le_queueLength_iff_le_hitEpoch
        q markedPath hhit_q m
    exact hiff.2 le_rfl
  have hcount_m_succ_le :
      postTagFalseMarkPrefixCount (m + 1) markedPath ≤ q + 1 := by
    rw [postTagFalseMarkPrefixCount_succ]
    have hif_le :
        (if (markedPath (Int.ofNat (m + 1))).2 = false then 1 else 0) ≤
          (1 : ℕ) := by
      split <;> omega
    omega
  by_contra hnot
  have hle_epoch :
      postTagFalseMarkHitEpoch (q + 1) markedPath ≤ m :=
    le_of_not_gt hnot
  have hcount_le :
      postTagFalseMarkPrefixCount
        (postTagFalseMarkHitEpoch (q + 1) markedPath + 1) markedPath ≤
        postTagFalseMarkPrefixCount (m + 1) markedPath :=
    postTagFalseMarkPrefixCount_monotone markedPath
      (Nat.succ_le_succ hle_epoch)
  have hspec :=
    postTagFalseMarkHitEpoch_spec (q + 1) markedPath hhit_succ
  omega

/-- Nonnegative all-event arrival epochs make the false-mark busy-until time
nonnegative. -/
theorem postTagFalseMarkBusyUntil_nonneg_of_arrivalTime_nonneg
    (q : ℕ) (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)))
    (harrival_nonneg :
      ∀ n : ℕ, 0 ≤ arrivalTime n (suspensionFuturePath path.1)) :
    0 ≤ postTagFalseMarkBusyUntil q path := by
  cases q with
  | zero =>
      simp [postTagFalseMarkBusyUntil]
  | succ q =>
      simpa [postTagFalseMarkBusyUntil, postTagFalseMarkResponse] using
        harrival_nonneg (postTagFalseMarkHitEpoch q path.2)

/-- Under monotone nonnegative all-event epochs, the false-mark busy-until time
precedes the tagged false-mark response whenever the requested response epoch
is reachable. -/
theorem postTagFalseMarkBusyUntil_le_response_of_arrivalTime_order
    (q : ℕ) (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)))
    (harrival_nonneg :
      ∀ n : ℕ, 0 ≤ arrivalTime n (suspensionFuturePath path.1))
    (harrival_mono : Monotone (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath path.1)))
    (hhit : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) path.2) :
    postTagFalseMarkBusyUntil q path ≤ postTagFalseMarkResponse q path := by
  cases q with
  | zero =>
      simpa [postTagFalseMarkBusyUntil, postTagFalseMarkResponse] using
        harrival_nonneg (postTagFalseMarkHitEpoch 0 path.2)
  | succ q =>
      have hepoch : postTagFalseMarkHitEpoch q path.2 ≤
          postTagFalseMarkHitEpoch (q + 1) path.2 :=
        postTagFalseMarkHitEpoch_mono_of_le (Nat.le_succ q) path.2 hhit
      simpa [postTagFalseMarkBusyUntil, postTagFalseMarkResponse] using
        harrival_mono hepoch

/--
Under strictly increasing positive all-event epochs, the false-mark
busy-until time strictly precedes the tagged false-mark response whenever the
requested response epoch is reachable.
-/
theorem postTagFalseMarkBusyUntil_lt_response_of_arrivalTime_strict
    (q : ℕ) (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)))
    (harrival_pos :
      ∀ n : ℕ, 0 < arrivalTime n (suspensionFuturePath path.1))
    (harrival_strict : StrictMono (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath path.1)))
    (hhit : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) path.2) :
    postTagFalseMarkBusyUntil q path < postTagFalseMarkResponse q path := by
  cases q with
  | zero =>
      simpa [postTagFalseMarkBusyUntil, postTagFalseMarkResponse] using
        harrival_pos (postTagFalseMarkHitEpoch 0 path.2)
  | succ q =>
      have hepoch :
          postTagFalseMarkHitEpoch q path.2 <
            postTagFalseMarkHitEpoch (q + 1) path.2 :=
        postTagFalseMarkHitEpoch_lt_succ_of_hit q path.2 hhit
      simpa [postTagFalseMarkBusyUntil, postTagFalseMarkResponse] using
        harrival_strict hepoch

/--
Positive service rate and strict false-mark timing make the tagged
false-mark work requirement strictly positive.
-/
theorem postTagFalseMarkTaggedServiceWork_zero_pos_of_busyUntil_lt_response
    {serviceRate : ℝ} {q : ℕ}
    {path : (ℤ → ℝ) × (ℤ → (ℕ × Bool))}
    (hserviceRate : 0 < serviceRate)
    (hbusy_lt_response :
      postTagFalseMarkBusyUntil q path < postTagFalseMarkResponse q path) :
    0 < postTagFalseMarkTaggedServiceWork serviceRate q path 0 := by
  simp [postTagFalseMarkTaggedServiceWork,
    mul_pos hserviceRate (sub_pos.mpr hbusy_lt_response)]

/--
Positive service rate and strict positive all-event epochs give positive
tagged false-mark work whenever the selected response false-mark is reachable.
-/
theorem postTagFalseMarkTaggedServiceWork_zero_pos_of_arrivalTime_strict
    {serviceRate : ℝ} (hserviceRate : 0 < serviceRate)
    (q : ℕ) (path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)))
    (harrival_pos :
      ∀ n : ℕ, 0 < arrivalTime n (suspensionFuturePath path.1))
    (harrival_strict : StrictMono (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath path.1)))
    (hhit : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) path.2) :
    0 < postTagFalseMarkTaggedServiceWork serviceRate q path 0 :=
  postTagFalseMarkTaggedServiceWork_zero_pos_of_busyUntil_lt_response
    hserviceRate
    (postTagFalseMarkBusyUntil_lt_response_of_arrivalTime_strict
      q path harrival_pos harrival_strict hhit)

/-- On a nonexplosive all-event clock path with enough false marks, the
false-mark stopping time has the exact strict response/count event identity. -/
theorem lt_postTagFalseMarkResponse_iff_postTagFalseMarkCount_le
    (q : ℕ) (gapPath : ℤ → ℝ) (markedPath : ℤ → (ℕ × Bool))
    (hdiv : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath gapPath)) atTop atTop)
    (hmono : Monotone (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath gapPath)))
    (hhit : ∃ n : ℕ, q < postTagFalseMarkPrefixCount (n + 1) markedPath)
    (t : ℝ) :
    t < postTagFalseMarkResponse q (gapPath, markedPath) ↔
      postTagFalseMarkCount t (gapPath, markedPath) ≤ q := by
  change t < arrivalTime (postTagFalseMarkHitEpoch q markedPath)
      (suspensionFuturePath gapPath) ↔
    postTagFalseMarkPrefixCount
      (canonicalRenewalCount t (suspensionFuturePath gapPath)) markedPath ≤ q
  rw [postTagFalseMarkPrefixCount_le_queueLength_iff_le_hitEpoch
    q markedPath hhit]
  constructor
  · intro ht
    apply Nat.le_of_not_gt
    intro hgt
    have htime : arrivalTime (postTagFalseMarkHitEpoch q markedPath)
        (suspensionFuturePath gapPath) ≤ t :=
      (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
        (suspensionFuturePath gapPath) hdiv hmono t
        (postTagFalseMarkHitEpoch q markedPath)).mp hgt
    exact (not_le_of_gt ht) htime
  · intro hcount
    apply lt_of_not_ge
    intro htime
    have hgt : postTagFalseMarkHitEpoch q markedPath <
        canonicalRenewalCount t (suspensionFuturePath gapPath) :=
      (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
        (suspensionFuturePath gapPath) hdiv hmono t
        (postTagFalseMarkHitEpoch q markedPath)).mpr htime
    exact (Nat.not_lt_of_ge hcount) hgt

/-- State-indexed form of the false-mark stopping-time identity. -/
theorem lt_postTagFalseMarkResponseFromState_iff_postTagFalseMarkCount_le
    (gapPath : ℤ → ℝ) (markedPath : ℤ → (ℕ × Bool))
    (hdiv : Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath gapPath)) atTop atTop)
    (hmono : Monotone (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath gapPath)))
    (hhit : ∃ n : ℕ, (markedPath 0).1 <
      postTagFalseMarkPrefixCount (n + 1) markedPath)
    (t : ℝ) :
    t < postTagFalseMarkResponseFromState (gapPath, markedPath) ↔
      postTagFalseMarkCount t (gapPath, markedPath) ≤ (markedPath 0).1 := by
  simpa [postTagFalseMarkResponseFromState] using
    (lt_postTagFalseMarkResponse_iff_postTagFalseMarkCount_le
      (markedPath 0).1 gapPath markedPath hdiv hmono hhit t)

private def falseMarkHitPredicate
    (x : ℕ × (ℤ → (ℕ × Bool))) (n : ℕ) : Prop :=
  x.1 < postTagFalseMarkPrefixCount (n + 1) x.2

private theorem measurableSet_falseMarkHitPredicate (n : ℕ) :
    MeasurableSet {x : ℕ × (ℤ → (ℕ × Bool)) |
      falseMarkHitPredicate x n} := by
  exact measurableSet_lt measurable_fst
    ((measurable_postTagFalseMarkPrefixCount (n + 1)).comp measurable_snd)

theorem measurable_postTagFalseMarkHitEpoch :
    Measurable (fun x : ℕ × (ℤ → (ℕ × Bool)) =>
      postTagFalseMarkHitEpoch x.1 x.2) := by
  classical
  refine measurable_to_countable' ?_
  intro k
  cases k with
  | zero =>
      have hpre :
          (fun x : ℕ × (ℤ → (ℕ × Bool)) =>
            postTagFalseMarkHitEpoch x.1 x.2) ⁻¹' ({0} : Set ℕ) =
            (⋃ n : ℕ, {x | falseMarkHitPredicate x n})ᶜ ∪
              {x | falseMarkHitPredicate x 0} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq]
        change postTagFalseMarkHitEpoch x.1 x.2 = 0 ↔
          (¬ ∃ n : ℕ, falseMarkHitPredicate x n) ∨ falseMarkHitPredicate x 0
        by_cases h : ∃ n : ℕ, falseMarkHitPredicate x n
        · have hraw : ∃ n : ℕ,
            x.1 < postTagFalseMarkPrefixCount (n + 1) x.2 := by
              simpa [falseMarkHitPredicate] using h
          rw [postTagFalseMarkHitEpoch, dif_pos hraw, Nat.find_eq_zero hraw]
          constructor
          · intro hzero
            exact Or.inr hzero
          · rintro (hnone | hzero)
            · exact (hnone hraw).elim
            · exact hzero
        · have hraw : ¬ ∃ n : ℕ,
            x.1 < postTagFalseMarkPrefixCount (n + 1) x.2 := by
              simpa [falseMarkHitPredicate] using h
          simp [postTagFalseMarkHitEpoch, hraw, h]
      rw [hpre]
      exact (MeasurableSet.iUnion measurableSet_falseMarkHitPredicate).compl.union
        (measurableSet_falseMarkHitPredicate 0)
  | succ k =>
      have hpre :
          (fun x : ℕ × (ℤ → (ℕ × Bool)) =>
            postTagFalseMarkHitEpoch x.1 x.2) ⁻¹' ({k + 1} : Set ℕ) =
            {x | falseMarkHitPredicate x (k + 1) ∧
              ∀ n < k + 1, ¬ falseMarkHitPredicate x n} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
        by_cases h : ∃ n : ℕ, falseMarkHitPredicate x n
        · have hraw : ∃ n : ℕ,
            x.1 < postTagFalseMarkPrefixCount (n + 1) x.2 := by
              simpa [falseMarkHitPredicate] using h
          rw [postTagFalseMarkHitEpoch, dif_pos hraw, Nat.find_eq_iff hraw]
          rfl
        · have hraw : ¬ ∃ n : ℕ,
            x.1 < postTagFalseMarkPrefixCount (n + 1) x.2 := by
              simpa [falseMarkHitPredicate] using h
          rw [postTagFalseMarkHitEpoch, dif_neg hraw]
          constructor
          · intro hzero
            omega
          · rintro ⟨hfirst, _⟩
            exact (h ⟨k + 1, hfirst⟩).elim
      rw [hpre]
      apply (measurableSet_falseMarkHitPredicate (k + 1)).inter
      have hforall :
          {x : ℕ × (ℤ → (ℕ × Bool)) |
            ∀ n < k + 1, ¬ falseMarkHitPredicate x n} =
          ⋂ n ∈ Finset.range (k + 1),
            {x | ¬ falseMarkHitPredicate x n} := by
        ext x
        simp
      change MeasurableSet {x : ℕ × (ℤ → (ℕ × Bool)) |
        ∀ n < k + 1, ¬ falseMarkHitPredicate x n}
      rw [hforall]
      apply Finset.measurableSet_biInter
      intro n _
      exact (measurableSet_falseMarkHitPredicate n).compl

/-- For a fixed pre-tag queue length, the literal false-mark stopping time is
measurable, including its zero fallback on paths with too few false marks. -/
theorem measurable_postTagFalseMarkResponse (q : ℕ) :
    Measurable (postTagFalseMarkResponse q) := by
  have harrival : Measurable (fun p : ℕ × (ℕ → ℝ) => arrivalTime p.1 p.2) :=
    measurable_from_prod_countable_right (fun n => measurable_arrivalTime n)
  have hhit : Measurable (fun path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      postTagFalseMarkHitEpoch q path.2) :=
    measurable_postTagFalseMarkHitEpoch.comp
      (measurable_const.prodMk measurable_snd)
  exact harrival.comp (hhit.prodMk
    (measurable_suspensionFuturePath.comp measurable_fst))

/-- The false-mark stopping time is measurable when its target number of
potential services is the literal pre-arrival queue state on the same path. -/
theorem measurable_postTagFalseMarkResponseFromState :
    Measurable (fun path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      postTagFalseMarkResponseFromState path) := by
  have harrival : Measurable (fun p : ℕ × (ℕ → ℝ) => arrivalTime p.1 p.2) :=
    measurable_from_prod_countable_right (fun n => measurable_arrivalTime n)
  have hstate : Measurable (fun path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      (path.2 0).1) :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hhit : Measurable (fun path : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      postTagFalseMarkHitEpoch (path.2 0).1 path.2) :=
    measurable_postTagFalseMarkHitEpoch.comp (hstate.prodMk measurable_snd)
  exact harrival.comp (hhit.prodMk
    (measurable_suspensionFuturePath.comp measurable_fst))

/-- An almost-sure nonexplosive clock and almost-sure existence of enough
false marks yield the actual strict response/count event identity for the
state-indexed false-mark stopping time. -/
theorem ae_lt_postTagFalseMarkResponseFromState_iff_postTagFalseMarkCount_le
    {P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))}
    (hdiv : ∀ᵐ path ∂P, Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath path.1)) atTop atTop)
    (hmono : ∀ᵐ path ∂P, Monotone (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath path.1)))
    (hhit : ∀ᵐ path ∂P, ∃ n : ℕ, (path.2 0).1 <
      postTagFalseMarkPrefixCount (n + 1) path.2)
    (t : ℝ) :
    {path | t < postTagFalseMarkResponseFromState path} =ᵐ[P]
      {path | postTagFalseMarkCount t path ≤ (path.2 0).1} := by
  filter_upwards [hdiv, hmono, hhit] with path hpath_div hpath_mono hpath_hit
  exact propext
    (lt_postTagFalseMarkResponseFromState_iff_postTagFalseMarkCount_le
      path.1 path.2 hpath_div hpath_mono hpath_hit t)

end

end AppliedModelingLib.Probability.Queueing

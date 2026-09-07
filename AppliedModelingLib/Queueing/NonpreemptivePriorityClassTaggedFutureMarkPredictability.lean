import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFixedReplayMeasurability
import AppliedModelingLib.Queueing.MulticlassPalmFutureMarkEquiv
import AppliedModelingLib.Foundations.Probability.IidPredictableStoppedReward

/-!
# Prefix dependence of finite priority replays

This module records the pathwise prefix-dependence facts used when one
passive class's post-origin work marks are exposed as an IID stream.  It is a
finite-trace interface only; passage to a stationary response is separate.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

/-- The external state together with the isolated passive class's future
unit-work stream. -/
abbrev MulticlassPalmFutureMarkFactorCarrier
    {Class : Type*} [Fintype Class] (i : Class) (j : {k : Class // k ≠ i}) :=
  ((((ℤ → ℝ) × (ℤ → ℝ)) ×
    ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
      stationaryPoissonWorkFutureMarkExternal)) × (ℕ → ℝ))

/-- The part of the future-mark factor that is visible before any isolated
future work coordinates are inspected. -/
abbrev MulticlassPalmFutureMarkExternalCarrier
    {Class : Type*} [Fintype Class] (i : Class) (j : {k : Class // k ≠ i}) :=
  (((ℤ → ℝ) × (ℤ → ℝ)) ×
    ((passiveMarkComplement i j → StationaryPoissonWorkPath) ×
      stationaryPoissonWorkFutureMarkExternal))

/-- The isolated passive class's forward renewal count through a deterministic
physical clock, read entirely from the external factor.  It is an upper bound
for the number of isolated positive labels strictly before that clock; the
weak endpoint convention is intentional and makes it stable at a clock
coinciding with an arrival. -/
noncomputable def multiclassPalmFutureMarkExternalFutureCountThrough
    {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i}) (t : ℝ) :
    MulticlassPalmFutureMarkExternalCarrier i j → ℕ :=
  fun s => Probability.PoissonProcess.canonicalRenewalCount
    ((s.2.2.1.1).1.2 + t)
    (Probability.PoissonProcess.suspensionFuturePath (s.2.2.1.1).1.1)

/-- The external deterministic-clock prefix count is Borel. -/
theorem measurable_multiclassPalmFutureMarkExternalFutureCountThrough
    {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i}) (t : ℝ) :
    Measurable (multiclassPalmFutureMarkExternalFutureCountThrough i j t) := by
  let p : MulticlassPalmFutureMarkExternalCarrier i j →
      Probability.PoissonProcess.GoodSuspensionState := fun s => s.2.2.1.1
  have hp : Measurable p := by
    exact measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp measurable_snd))
  change Measurable (fun s => Probability.PoissonProcess.canonicalRenewalCount
    ((p s).1.2 + t) (Probability.PoissonProcess.suspensionFuturePath (p s).1.1))
  exact Probability.PoissonProcess.measurable_jointCanonicalRenewalCount.comp
    ((((measurable_snd.comp measurable_subtype_coe).comp hp).add_const t).prodMk
      (Probability.PoissonProcess.measurable_suspensionFuturePath.comp
        ((measurable_fst.comp measurable_subtype_coe).comp hp)))

/-- Every isolated positive label arriving strictly before a deterministic
clock lies below the external forward-renewal count through that clock. -/
theorem lt_multiclassPalmFutureMarkExternalFutureCountThrough_of_arrival_lt
    {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureMarkFactorCarrier i j) (r : ℕ) (t : ℝ)
    (hbefore : stationaryPriorityClassTaggedArrival i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
      j.1 (Int.ofNat (r + 1)) < t) :
    r < multiclassPalmFutureMarkExternalFutureCountThrough i j t x.1 := by
  have harrival : Probability.PoissonProcess.suspensionBaseArrival
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1
      (Int.ofNat (r + 1)) < t := by
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg j.2] using hbefore
  have hcount :=
    Probability.PoissonProcess.lt_canonicalRenewalCount_of_suspensionBaseArrival_ofNat_succ_lt
      (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1 r t
      harrival
  simpa [multiclassPalmFutureMarkExternalFutureCountThrough,
    multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival] using hcount

/-- Complete a finite future-mark prefix by assigning zero to every
unobserved coordinate.  This is a Borel representative used only to expose
finite-prefix observables; the pathwise prefix theorem below proves that the
representative's tail is irrelevant to the strict finite replay. -/
def futureMarkPrefixZeroExtension (N : ℕ) (u : Finset.range N → ℝ) : ℕ → ℝ :=
  fun r => if hr : r < N then u ⟨r, Finset.mem_range.mpr hr⟩ else 0

/-- Finite-prefix zero completion is Borel. -/
theorem measurable_futureMarkPrefixZeroExtension (N : ℕ) :
    Measurable (futureMarkPrefixZeroExtension N) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r < N
  · simpa [futureMarkPrefixZeroExtension, dif_pos hr] using
      (measurable_pi_apply (X := fun _ : Finset.range N => ℝ)
        ⟨r, Finset.mem_range.mpr hr⟩)
  · simp [futureMarkPrefixZeroExtension, dif_neg hr]

/-- Reassemble a factored carrier from its external state and a visible
finite future-mark prefix, assigning an arbitrary fixed tail. -/
def multiclassPalmFutureMarkPrefixRepresentative
    {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i}) (N : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range N → ℝ) →
      MulticlassPalmFutureMarkFactorCarrier i j :=
  fun x => (x.1, futureMarkPrefixZeroExtension N x.2)

/-- The finite-prefix representative is Borel. -/
theorem measurable_multiclassPalmFutureMarkPrefixRepresentative
    {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i}) (N : ℕ) :
    Measurable (multiclassPalmFutureMarkPrefixRepresentative i j N) := by
  exact measurable_fst.prodMk
    ((measurable_futureMarkPrefixZeroExtension N).comp measurable_snd)

/-- The Borel selected-customer completion observation obtained from the
external factor and the first `N` isolated future marks.  The observation is
made strictly before the `(N+1)`st isolated passive arrival. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkPrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range N → ℝ) → ℝ :=
  fun x =>
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm
        (multiclassPalmFutureMarkPrefixRepresentative i j N x)) older
      (stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm
          (multiclassPalmFutureMarkPrefixRepresentative i j N x))
        j.1 (Int.ofNat (N + 1)))).getD 0

/-- The finite-prefix selected completion observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkPrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkPrefixCompletion
      meanService i j older N) := by
  apply (measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_atArrival
    meanService i j.1 (Int.ofNat (N + 1)) older).comp
  exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm.measurable.comp
    (measurable_multiclassPalmFutureMarkPrefixRepresentative i j N)

/-- The zero-tail prefix representative agrees with a factored carrier on
every one of its first `N` isolated future work coordinates. -/
theorem futureMarkPrefixZeroExtension_eq_of_lt
    (N : ℕ) (u : Finset.range N → ℝ) (r : ℕ) (hr : r < N) :
    futureMarkPrefixZeroExtension N u r = u ⟨r, Finset.mem_range.mpr hr⟩ := by
  simp [futureMarkPrefixZeroExtension, hr]

/-- Under the factored selected-Palm law, the reconstructed finite replay
input is almost surely a good suspension path with strictly positive scaled
service work at every labelled customer. -/
theorem ae_multiclassPalmFutureMarkFactor_good_and_positive
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      Probability.PoissonProcess.suspensionGoodGapPath
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1 ∧
      ∀ k l, 0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) k l := by
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  let μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let ν := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hpres : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
        arrivalRate harrivalRate i j)
  have hsource : ∀ᵐ z ∂μ,
      Probability.PoissonProcess.suspensionGoodGapPath z.1.1 ∧
      ∀ k l, 0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z k l := by
    filter_upwards [
      ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
        arrivalRate harrivalRate i,
      ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
        arrivalRate meanService harrivalRate hmeanService i] with z hgood hpositive
    exact ⟨hgood, hpositive⟩
  have hback : MeasurePreserving e.symm ν μ := by
    exact hpres.symm e
  rw [← hback.map_eq] at hsource
  exact ae_of_ae_map hback.measurable.aemeasurable hsource

/-- A finite classwise arrival window is fixed once every arrival path is
fixed. -/
theorem stationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrivalPaths_eq
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hselected : z.1 = w.1)
    (hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1) :
    stationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      stationaryPriorityClassTaggedArrivalWindowIndices i w a b := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [stationaryPriorityClassTaggedArrivalWindowIndices, hselected]
  · have hpath := hpassive k hki
    unfold stationaryPriorityClassTaggedArrivalWindowIndices
    simp only [dif_neg hki]
    change Probability.PoissonProcess.suspensionBaseArrivalIndices a b
      (z.2 ⟨k, hki⟩).1 =
      Probability.PoissonProcess.suspensionBaseArrivalIndices a b
        (w.2 ⟨k, hki⟩).1
    rw [hpath]

/-- The canonical order of a finite arrival window is fixed once every
arrival path is fixed. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrivalPaths_eq
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hselected : z.1 = w.1)
    (hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1) :
    canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i w a b := by
  have hledger := stationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrivalPaths_eq
    i z w a b hselected hpassive
  have harrival : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m =
        stationaryPriorityClassTaggedArrival i w k m := by
    intro k m
    by_cases hki : k = i
    · subst k
      simp [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival, hselected]
    · have hpath := hpassive k hki
      unfold stationaryPriorityClassTaggedArrival
        multiclassStationaryPoissonWorkClassTaggedArrival
      simp only [dif_neg hki]
      change Probability.PoissonProcess.suspensionBaseArrival
        (z.2 ⟨k, hki⟩).1 m =
        Probability.PoissonProcess.suspensionBaseArrival
          (w.2 ⟨k, hki⟩).1 m
      rw [hpath]
  have horder : stationaryPriorityClassTaggedArrivalIndexLE i z =
      stationaryPriorityClassTaggedArrivalIndexLE i w := by
    funext first second
    unfold stationaryPriorityClassTaggedArrivalIndexLE
      stationaryPriorityClassTaggedArrivalIndexKey
    rw [harrival first.1 first.2, harrival second.1 second.2]
  classical
  simp only [canonicalStationaryPriorityClassTaggedArrivalWindowIndices]
  rw [hledger]
  let s := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedArrivalWindowIndices i w a b)
  let rz := stationaryPriorityClassTaggedArrivalIndexLE i z
  let rw' := stationaryPriorityClassTaggedArrivalIndexLE i w
  have horder' : rz = rw' := horder
  letI : DecidableRel rz := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rz :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm rz :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total rz :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  letI : DecidableRel rw' := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rw' :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i w⟩
  letI : Std.Antisymm rw' :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i w⟩
  letI : Std.Total rw' :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i w⟩
  change s.sort rz = s.sort rw'
  have hperm : List.Perm (s.sort rz) (s.sort rw') :=
    (Finset.sort_perm_toList s rz).trans (Finset.sort_perm_toList s rw').symm
  have hleft : (s.sort rz).Pairwise rz := Finset.pairwise_sort s rz
  have hrightw : (s.sort rw').Pairwise rw' := Finset.pairwise_sort s rw'
  have hright : (s.sort rw').Pairwise rz := by
    apply hrightw.imp
    intro first second hfirst
    exact horder'.symm ▸ hfirst
  exact hperm.eq_of_pairwise' hleft hright

/-- Once a canonical window index ledger agrees, equality of its arrival and
work coordinates gives equality of the corresponding executable job ledger. -/
theorem canonicalStationaryPriorityClassTaggedArrivalWindowJobs_eq_of_indices_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ)
    (hindices : canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowIndices i w a b)
    (harrival : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m =
        stationaryPriorityClassTaggedArrival i w k m)
    (hwork : ∀ q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b,
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w q.1 q.2) :
    canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i w a b := by
  unfold canonicalStationaryPriorityClassTaggedArrivalWindowJobs
  rw [hindices]
  apply List.map_congr_left
  intro q hq
  have hqz : q ∈ canonicalStationaryPriorityClassTaggedArrivalWindowIndices i z a b := by
    rwa [hindices]
  rw [harrival q.1 q.2, hwork q hqz]

/-- Equal finite window job ledgers yield equal finite deterministic queue
states. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_jobs_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ)
    (hjobs : canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b =
      canonicalStationaryPriorityClassTaggedArrivalWindowJobs meanService i w a b) :
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z a b =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w a b := by
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  rw [hjobs]

/-- A finite pre-zero replay is fixed by the external component of the
future-mark factor.  Its isolated passive jobs have nonpositive labels. -/
theorem canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_futureMark_factor
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (older : ℝ)
    (hxy : x.1 = y.1)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1) :
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) (-older) 0 := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let w := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y
  change canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
    canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0
  have hgoodz : Probability.PoissonProcess.suspensionGoodGapPath z.1.1 := by
    simpa [z] using hgood
  have hselected : z.1 = w.1 := by
    simpa [z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath_eq_of_fst_eq
        i j x y hxy)
  have hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1 := by
    intro k hki
    by_cases hkj : (⟨k, hki⟩ : {l : Fin n // l ≠ i}) = j
    · subst j
      simpa [z, w] using
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival_eq_of_fst_eq
          i ⟨k, hki⟩ x y hxy)
    · have hpath :=
        multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath_eq_of_fst_eq
          i j x y ⟨k, hki⟩ hkj hxy
      exact congrArg Prod.fst (by simpa [z, w] using hpath)
  have hindices := canonicalStationaryPriorityClassTaggedArrivalWindowIndices_eq_of_arrivalPaths_eq
    i z w (-older) 0 hselected hpassive
  apply canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_jobs_eq meanService i z w
    (-older) 0
  apply canonicalStationaryPriorityClassTaggedArrivalWindowJobs_eq_of_indices_eq
    meanService i z w (-older) 0 hindices
  · intro k m
    simpa [z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
        i j x y k m hxy)
  · intro q hq
    rcases q with ⟨k, m⟩
    dsimp only
    by_cases hki : k = i
    · subst k
      exact congrArg (fun r => meanService i * r)
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
          i j x y m hxy)
    · by_cases hkj : (⟨k, hki⟩ : {l : Fin n // l ≠ i}) = j
      · subst j
        have hbefore : stationaryPriorityClassTaggedArrival i z k m < 0 :=
          canonicalStationaryPriorityClassTaggedArrivalIndex_lt_right
            i z (-older) 0 hgoodz (Sigma.mk k m) hq
        have hbeforePassive : Probability.PoissonProcess.suspensionBaseArrival
            (z.2 ⟨k, hki⟩).1 m < 0 := by
          simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hki] using hbefore
        have hnonpos : m ≤ 0 :=
          Probability.PoissonProcess.le_zero_of_suspensionBaseArrival_lt_zero
            (z.2 ⟨k, hki⟩).1 m hbeforePassive
        cases m with
        | ofNat m =>
            have hmzero : m = 0 := by
              apply Nat.eq_zero_of_le_zero
              exact Int.ofNat_le.mp hnonpos
            subst m
            exact congrArg (fun r => meanService k * r)
              (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginRequirement_eq_of_fst_eq
                i ⟨k, hki⟩ x y hxy)
        | negSucc r =>
            exact congrArg (fun a => meanService k * a)
              (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastRequirement_eq_of_fst_eq
                i ⟨k, hki⟩ x y r hxy)
      · exact congrArg (fun r => meanService k * r)
          (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassiveRequirement_eq_of_fst_eq
            i j x y k hki hkj m hxy)

/-- A strict future index ledger is fixed once every arrival path and its
queried horizon are fixed. -/
theorem stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrivalPaths_eq
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (ht : t = u)
    (hselected : z.1 = w.1)
    (hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1) :
    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t =
      stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w u := by
  subst u
  funext k
  by_cases hki : k = i
  · subst k
    simp [stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
      stationaryPriorityClassTaggedFutureArrivalIndices, hselected,
      stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival]
  · have hpath := hpassive k hki
    unfold stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      stationaryPriorityClassTaggedFutureArrivalIndices
      stationaryPriorityClassTaggedArrival
      multiclassStationaryPoissonWorkClassTaggedArrival
    simp only [dif_neg hki]
    change (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 t
      (z.2 ⟨k, hki⟩).1).filter
        (fun r => Probability.PoissonProcess.suspensionBaseArrival
          (z.2 ⟨k, hki⟩).1 r < t) =
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 t
        (w.2 ⟨k, hki⟩).1).filter
          (fun r => Probability.PoissonProcess.suspensionBaseArrival
            (w.2 ⟨k, hki⟩).1 r < t)
    rw [hpath]

/-- The canonical strict future ledger is fixed once every arrival path and
its queried horizon are fixed. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrivalPaths_eq
    {n : ℕ} (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ) (ht : t = u)
    (hselected : z.1 = w.1)
    (hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1) :
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w u := by
  subst u
  have hledger :=
    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrivalPaths_eq
      i z w t t rfl hselected hpassive
  have harrival : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m =
        stationaryPriorityClassTaggedArrival i w k m := by
    intro k m
    by_cases hki : k = i
    · subst k
      simp [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival, hselected]
    · have hpath := hpassive k hki
      unfold stationaryPriorityClassTaggedArrival
        multiclassStationaryPoissonWorkClassTaggedArrival
      simp only [dif_neg hki]
      change Probability.PoissonProcess.suspensionBaseArrival
        (z.2 ⟨k, hki⟩).1 m =
        Probability.PoissonProcess.suspensionBaseArrival
          (w.2 ⟨k, hki⟩).1 m
      rw [hpath]
  have horder : stationaryPriorityClassTaggedArrivalIndexLE i z =
      stationaryPriorityClassTaggedArrivalIndexLE i w := by
    funext first second
    unfold stationaryPriorityClassTaggedArrivalIndexLE
      stationaryPriorityClassTaggedArrivalIndexKey
    rw [harrival first.1 first.2, harrival second.1 second.2]
  classical
  simp only [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon]
  rw [hledger]
  let s := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w t)
  let rz := stationaryPriorityClassTaggedArrivalIndexLE i z
  let rw' := stationaryPriorityClassTaggedArrivalIndexLE i w
  have horder' : rz = rw' := horder
  letI : DecidableRel rz := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rz :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm rz :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total rz :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  letI : DecidableRel rw' := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n) rw' :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i w⟩
  letI : Std.Antisymm rw' :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i w⟩
  letI : Std.Total rw' :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i w⟩
  change s.sort rz = s.sort rw'
  have hperm : List.Perm (s.sort rz) (s.sort rw') :=
    (Finset.sort_perm_toList s rz).trans (Finset.sort_perm_toList s rw').symm
  have hleft : (s.sort rz).Pairwise rz := Finset.pairwise_sort s rz
  have hrightw : (s.sort rw').Pairwise rw' := Finset.pairwise_sort s rw'
  have hright : (s.sort rw').Pairwise rz := by
    apply hrightw.imp
    intro first second hfirst
    exact horder'.symm ▸ hfirst
  exact hperm.eq_of_pairwise' hleft hright

/-- Once a strict canonical index ledger agrees, equality of its arrival and
work coordinates gives equality of the corresponding executable job ledger. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_indices_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t u : ℝ)
    (hindices : canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i w u)
    (harrival : ∀ (k : Fin n) (m : ℤ),
      stationaryPriorityClassTaggedArrival i z k m =
        stationaryPriorityClassTaggedArrival i w k m)
    (hwork : ∀ q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon i z t,
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w q.1 q.2) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w u := by
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
  rw [hindices]
  apply List.map_congr_left
  intro q hq
  have hqz : q ∈ canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
      i z t := by
    rwa [hindices]
  rw [harrival q.1 q.2, hwork q hqz]

/-- A finite strict replay up to the `N + 1`st arrival of an isolated passive
class uses only the first `N` future work coordinates of that class. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_futureMark_prefix
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (N : ℕ)
    (hxy : x.1 = y.1) (hprefix : ∀ r < N, x.2 r = y.2 r) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1))) =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
          j.1 (Int.ofNat (N + 1))) := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let w := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y
  let t := stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))
  let u := stationaryPriorityClassTaggedArrival i w j.1 (Int.ofNat (N + 1))
  change canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w u
  have htime : t = u := by
    simpa [t, z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
        i j x y j.1 (Int.ofNat (N + 1)) hxy)
  have hselected : z.1 = w.1 := by
    simpa [z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath_eq_of_fst_eq
        i j x y hxy)
  have hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1 := by
    intro k hki
    by_cases hkj : (⟨k, hki⟩ : {l : Fin n // l ≠ i}) = j
    · subst j
      simpa [z, w] using
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival_eq_of_fst_eq
          i ⟨k, hki⟩ x y hxy)
    · have hpath :=
        multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath_eq_of_fst_eq
          i j x y ⟨k, hki⟩ hkj hxy
      exact congrArg Prod.fst (by simpa [z, w] using hpath)
  have hindices :=
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrivalPaths_eq
      i z w t u htime hselected hpassive
  apply canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_indices_eq
    meanService i z w t u hindices
  · intro k m
    simpa [z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
        i j x y k m hxy)
  · intro q hq
    rcases q with ⟨k, m⟩
    dsimp only
    by_cases hki : k = i
    · subst k
      exact congrArg (fun r => meanService i * r)
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
          i j x y m hxy)
    · by_cases hkj : (⟨k, hki⟩ : {l : Fin n // l ≠ i}) = j
      · subst j
        cases m with
        | ofNat m =>
            cases m with
            | zero =>
                exact congrArg (fun r => meanService k * r)
                  (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginRequirement_eq_of_fst_eq
                    i ⟨k, hki⟩ x y hxy)
            | succ r =>
                have hltInt : Int.ofNat (r + 1) < Int.ofNat (N + 1) :=
                  stationaryPriorityClassTaggedFutureArrivalIndex_lt_of_mem_beforeHorizon
                    i k hki z (Int.ofNat (r + 1)) (Int.ofNat (N + 1)) (by
                      simpa [t] using hq)
                have hlt : r < N :=
                  Nat.lt_of_succ_lt_succ (by
                    simpa [Nat.succ_eq_add_one] using (Int.ofNat_lt.mp hltInt))
                exact congrArg (fun a => meanService k * a)
                  (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveFutureRequirement_eq_of_prefix
                    i ⟨k, hki⟩ x y N r hlt hprefix)
        | negSucc r =>
            exact congrArg (fun a => meanService k * a)
              (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastRequirement_eq_of_fst_eq
                i ⟨k, hki⟩ x y r hxy)
      · exact congrArg (fun r => meanService k * r)
          (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassiveRequirement_eq_of_fst_eq
            i j x y k hki hkj m hxy)

/-- A strict finite replay through any deterministic clock uses only the
isolated future work marks whose labelled arrivals occur strictly before that
clock.  The explicit bound avoids treating a random number of inspected marks
as if it were a deterministic prefix. -/
theorem canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_futureMark_prefix_of_bound
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (N : ℕ) (t : ℝ)
    (hxy : x.1 = y.1) (hprefix : ∀ r < N, x.2 r = y.2 r)
    (hbound : ∀ r,
      stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (r + 1)) < t → r < N) :
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) t := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let w := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y
  change canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
    canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i w t
  have hselected : z.1 = w.1 := by
    simpa [z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedPath_eq_of_fst_eq
        i j x y hxy)
  have hpassive : ∀ (k : Fin n) (hki : k ≠ i),
      (z.2 ⟨k, hki⟩).1 = (w.2 ⟨k, hki⟩).1 := by
    intro k hki
    by_cases hkj : (⟨k, hki⟩ : {l : Fin n // l ≠ i}) = j
    · subst j
      simpa [z, w] using
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveArrival_eq_of_fst_eq
          i ⟨k, hki⟩ x y hxy)
    · have hpath :=
        multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassivePath_eq_of_fst_eq
          i j x y ⟨k, hki⟩ hkj hxy
      exact congrArg Prod.fst (by simpa [z, w] using hpath)
  have hindices :=
    canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon_eq_of_arrivalPaths_eq
      i z w t t rfl hselected hpassive
  apply canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_indices_eq
    meanService i z w t t hindices
  · intro k m
    simpa [z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
        i j x y k m hxy)
  · intro q hq
    rcases q with ⟨k, m⟩
    dsimp only
    by_cases hki : k = i
    · subst k
      exact congrArg (fun r => meanService i * r)
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
          i j x y m hxy)
    · by_cases hkj : (⟨k, hki⟩ : {l : Fin n // l ≠ i}) = j
      · subst j
        cases m with
        | ofNat m =>
            cases m with
            | zero =>
                exact congrArg (fun r => meanService k * r)
                  (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveOriginRequirement_eq_of_fst_eq
                    i ⟨k, hki⟩ x y hxy)
            | succ r =>
                have hqindex : Int.ofNat (r + 1) ∈
                    stationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
                      i z t k := by
                  simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon,
                    nonpreemptivePriorityArrivalWindowIndices] using hq
                have htime : stationaryPriorityClassTaggedArrival i z k
                    (Int.ofNat (r + 1)) < t :=
                  (Finset.mem_filter.mp hqindex).2
                have hlt : r < N := by
                  simpa [z] using hbound r (by simpa using htime)
                exact congrArg (fun a => meanService k * a)
                  (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passiveFutureRequirement_eq_of_prefix
                    i ⟨k, hki⟩ x y N r hlt hprefix)
        | negSucc r =>
            exact congrArg (fun a => meanService k * a)
              (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_passivePastRequirement_eq_of_fst_eq
                i ⟨k, hki⟩ x y r hxy)
      · exact congrArg (fun r => meanService k * r)
          (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_otherPassiveRequirement_eq_of_fst_eq
            i j x y k hki hkj m hxy)

/-- Equality of the pre-zero finite state and of the strict future job ledger
propagates through the deterministic strict replay. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_pastState_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t u : ℝ) (ht : t = u)
    (hpast : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0)
    (htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w)
    (hfuture : canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w u) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i z older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i w older u := by
  subst u
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
  rw [hpast, htag, hfuture]

/-- Under the same two finite-input equalities, the strict replay has the
same selected-customer completion observation. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_eq_of_pastState_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t u : ℝ) (ht : t = u)
    (hpast : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0)
    (htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w)
    (hfuture : canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w u) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i z older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i w older u := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_pastState_eq
    meanService i z w older t u ht hpast htag hfuture]

/-- A finite replay at a deterministic clock is unchanged when the external
arrival data agree and the isolated future-mark prefix covers every such
arrival before that clock. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_futureMark_prefix_of_bound
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (N : ℕ) (older t : ℝ)
    (hxy : x.1 = y.1) (hprefix : ∀ r < N, x.2 r = y.2 r)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1)
    (hbound : ∀ r,
      stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (r + 1)) < t → r < N) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
        older t := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let w := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y
  change stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t =
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i w older t
  have hpast : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0 := by
    simpa [z, w] using
      (canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_futureMark_factor
        meanService i j x y older hxy hgood)
  have htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w := by
    unfold stationaryPriorityClassTaggedJob
    rw [show stationaryPriorityClassTaggedArrival i z i 0 =
        stationaryPriorityClassTaggedArrival i w i 0 by
      simpa [z, w] using
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
          i j x y i 0 hxy)]
    rw [show stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w i 0 by
      exact congrArg (fun r => meanService i * r)
        (by simpa [z, w] using
          (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
            i j x y 0 hxy))]
  have hfuture : canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w t := by
    simpa [z, w] using
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_futureMark_prefix_of_bound
        meanService i j x y N t hxy hprefix hbound)
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_pastState_eq
    meanService i z w older t t rfl hpast htag hfuture

/-- For every fixed remote-past cutoff, the strict replay before an isolated
passive arrival is a function of the external factor and the preceding IID
work prefix. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_eq_of_futureMark_prefix
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (N : ℕ) (older : ℝ)
    (hxy : x.1 = y.1) (hprefix : ∀ r < N, x.2 r = y.2 r)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1))) =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
          j.1 (Int.ofNat (N + 1))) := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let w := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y
  let t := stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))
  let u := stationaryPriorityClassTaggedArrival i w j.1 (Int.ofNat (N + 1))
  change stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i z older t =
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i w older u
  have ht : t = u := by
    simpa [t, z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
        i j x y j.1 (Int.ofNat (N + 1)) hxy)
  have hpast : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0 := by
    simpa [z, w] using
      (canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_futureMark_factor
        meanService i j x y older hxy hgood)
  have htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w := by
    unfold stationaryPriorityClassTaggedJob
    rw [show stationaryPriorityClassTaggedArrival i z i 0 =
        stationaryPriorityClassTaggedArrival i w i 0 by
      simpa [z, w] using
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
          i j x y i 0 hxy)]
    rw [show stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w i 0 by
      exact congrArg (fun r => meanService i * r)
        (by simpa [z, w] using
          (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
            i j x y 0 hxy))]
  have hfuture : canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w u := by
    simpa [z, w, t, u] using
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_futureMark_prefix
        meanService i j x y N hxy hprefix)
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_eq_of_pastState_eq
    meanService i z w older t u ht hpast htag hfuture

/-- On a good selected suspension, the literal strict finite replay before
the `(N+1)`st isolated passive arrival is exactly the Borel observable of the
external factor and first `N` isolated future marks. -/
theorem stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_of_good
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1) :
    stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older N
      (x.1, fun r => x.2 r) =
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1)))).getD 0 := by
  let y : MulticlassPalmFutureMarkFactorCarrier i j :=
    multiclassPalmFutureMarkPrefixRepresentative i j N (x.1, fun r => x.2 r)
  have hfst : x.1 = y.1 := by
    rfl
  have hprefix : ∀ r < N, x.2 r = y.2 r := by
    intro r hr
    change x.2 r = futureMarkPrefixZeroExtension N (fun s => x.2 s) r
    rw [futureMarkPrefixZeroExtension_eq_of_lt N (fun s => x.2 s) r hr]
  have heq :=
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_eq_of_futureMark_prefix
      meanService i j x y N older hfst hprefix hgood
  change (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) older
      (stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
        j.1 (Int.ofNat (N + 1)))).getD 0 = _
  rw [heq]

/-- On the good positive-work carrier, the Borel prefix completion observable
vanishes exactly while the literal strict replay has not recorded the tagged
completion.  The zero-filled unobserved tail is harmless here: prefix
dependence first replaces it by the actual future-mark path, and the temporal
ledger invariant then rules out a physical completion at zero. -/
theorem stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_zero_iff_of_good_positive
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (holder : 0 ≤ older)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1)
    (hpositive : ∀ k l,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) k l) :
    stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older N
      (x.1, fun r => x.2 r) = 0 ↔
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1))) = none := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let t := stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))
  have ht : 0 ≤ t := by
    have htpos : 0 < t := by
      dsimp [t, z, stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival]
      rw [dif_neg j.2]
      exact Probability.PoissonProcess.zero_lt_suspensionBaseArrival_ofNat_succ
        (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1 N
    exact htpos.le
  rw [stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_of_good
    meanService i j older N x hgood]
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_getD_eq_zero_iff
    meanService i z older t holder ht hgood hpositive

/-- Equivalently, a nonzero Borel prefix observation is exactly a recorded
tagged completion in the literal strict replay. -/
theorem stationaryPriorityClassTaggedFutureMarkPrefixCompletion_ne_zero_iff_of_good_positive
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (holder : 0 ≤ older)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1)
    (hpositive : ∀ k l,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) k l) :
    stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older N
      (x.1, fun r => x.2 r) ≠ 0 ↔
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1))) ≠ none := by
  exact not_congr
    (stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_zero_iff_of_good_positive
      meanService i j older N x holder hgood hpositive)

/-- The finite-prefix completion semantics hold simultaneously at every
isolated future arrival under the factored selected-Palm product law. -/
theorem ae_forall_stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_zero_iff
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (older : ℝ) (holder : 0 ≤ older) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ N,
        stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older N
          (x.1, fun r => x.2 r) = 0 ↔
        stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
          meanService i ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          older
          (stationaryPriorityClassTaggedArrival i
            ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
            j.1 (Int.ofNat (N + 1))) = none := by
  filter_upwards [ae_multiclassPalmFutureMarkFactor_good_and_positive
    arrivalRate meanService harrivalRate hmeanService i j] with x hx
  rcases hx with ⟨hgood, hpositive⟩
  intro N
  exact stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_zero_iff_of_good_positive
    meanService i j older N x holder hgood hpositive

/-- Along diagonal remote-past horizons, the factored finite-prefix
completion observation is almost surely eventually nonzero.  Thus the
renewal-indexed tagged completion is finite on the genuine stationary queue,
before any expectation or summability claim is made. -/
theorem ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixCompletion_ne_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ᶠ N : ℕ in Filter.atTop,
        stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j (N : ℝ) N
          (x.1, fun r => x.2 r) ≠ 0 := by
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  let μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let ν := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hpres : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
        arrivalRate harrivalRate i j)
  have hsource : ∀ᵐ z ∂μ, ∀ᶠ N : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i z (N : ℝ)
        (stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))) ≠ none := by
    simpa [μ] using
      (ae_eventually_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon_ne_none_at_passiveArrival
        arrivalRate meanService harrivalRate hmeanService hstable i j)
  have hback : MeasurePreserving e.symm ν μ := hpres.symm e
  rw [← hback.map_eq] at hsource
  have hfactor : ∀ᵐ x ∂ν, ∀ᶠ N : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i (e.symm x) (N : ℝ)
        (stationaryPriorityClassTaggedArrival i (e.symm x) j.1 (Int.ofNat (N + 1))) ≠ none :=
    ae_of_ae_map hback.measurable.aemeasurable hsource
  filter_upwards [hfactor,
    ae_multiclassPalmFutureMarkFactor_good_and_positive
      arrivalRate meanService harrivalRate hmeanService i j] with x hfinite hx
  rcases hx with ⟨hgood, hpositive⟩
  filter_upwards [hfinite] with N hN
  intro hzero
  apply hN
  exact (stationaryPriorityClassTaggedFutureMarkPrefixCompletion_eq_zero_iff_of_good_positive
    meanService i j (N : ℝ) N x (Nat.cast_nonneg N) hgood hpositive).mp hzero

/-- Evaluate the finite-prefix completion observable on an external state and
an entire IID stream by retaining only its first `N` coordinates. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkPrefixObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
  fun z => stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older N
    (z.1, fun r => z.2 r)

/-- The finite-prefix observation is Borel on the external-state/IID-stream
carrier. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkPrefixObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkPrefixObservation
      meanService i j older N) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixCompletion
    meanService i j older N).comp
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro r
  exact (measurable_pi_apply (X := fun _ : ℕ => ℝ) r).comp measurable_snd

/-- The diagonal version of the finite-prefix completion observation.  At
index `N` it uses both a remote-past horizon `N` and the strict replay before
the `(N+1)`st isolated passive arrival. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (N : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
  fun z => stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j (N : ℝ) N
    (z.1, fun r => z.2 r)

/-- Each diagonal finite-prefix observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation
      meanService i j N) := by
  exact measurable_stationaryPriorityClassTaggedFutureMarkPrefixObservation
    meanService i j (N : ℝ) N

/-- The diagonal Borel observations become nonzero almost surely eventually
under strict load. -/
theorem ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_ne_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ᶠ N : ℕ in Filter.atTop,
        stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j N x ≠ 0 := by
  simpa [stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation] using
    (ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixCompletion_ne_zero
      arrivalRate meanService harrivalRate hmeanService hstable i j)

/-- The finite-prefix observation after `N+1` coordinates is literally the
finite-prefix completion function applied to the inspected IID prefix through
coordinate `N`. -/
theorem stationaryPriorityClassTaggedFutureMarkPrefixObservation_succ
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older (N + 1) z =
      stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older (N + 1)
        (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
          MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) := by
  rfl

/-- The unique empty future-mark prefix. -/
def emptyFutureMarkPrefix : Finset.range 0 → ℝ :=
  fun r => False.elim (Nat.not_lt_zero r.1 (Finset.mem_range.mp r.2))

/-- The zero-coordinate completion observation uses only the external
factor. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) :
    MulticlassPalmFutureMarkExternalCarrier i j → ℝ :=
  fun s => stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older 0
    (s, emptyFutureMarkPrefix)

/-- The zero-coordinate completion observation is Borel on the external
factor. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
      meanService i j older) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixCompletion
    meanService i j older 0).comp
  exact measurable_id.prodMk measurable_const

/-- At coordinate zero, the stream-level observation is the external
zero-prefix observation. -/
theorem stationaryPriorityClassTaggedFutureMarkPrefixObservation_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older 0 z =
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older z.1 := by
  unfold stationaryPriorityClassTaggedFutureMarkPrefixObservation
    stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
  apply congrArg (stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older 0)
  apply Prod.ext
  · rfl
  · funext r
    exact False.elim (Nat.not_lt_zero r.1 (Finset.mem_range.mp r.2))

/-- The bounded first observation index at which the selected completion
observable is nonzero.  It equals the deterministic cap when no such
observation occurs before that cap. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkCappedStop
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℕ := by
  classical
  intro z
  exact if h : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older m z ≠ 0
    then Nat.find h else cap

/-- Continuing strictly before a capped first-nonzero observation means that
the cap has not been reached and that every observable completion through
the queried coordinate is still zero. -/
theorem lt_stationaryPriorityClassTaggedFutureMarkCappedStop_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap q : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    q < stationaryPriorityClassTaggedFutureMarkCappedStop meanService i j older cap z ↔
      q < cap ∧ ∀ m ≤ q,
        stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older m z = 0 := by
  classical
  unfold stationaryPriorityClassTaggedFutureMarkCappedStop
  by_cases h : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older m z ≠ 0
  · rw [dif_pos h]
    constructor
    · intro hq
      rcases Nat.find_spec h with ⟨hcap, hne⟩
      refine ⟨lt_of_lt_of_le hq (Nat.le_of_lt hcap), ?_⟩
      intro m hm
      by_contra hzero
      have hmcap : m < cap :=
        lt_of_le_of_lt hm (lt_of_lt_of_le hq (Nat.le_of_lt hcap))
      have hmin : Nat.find h ≤ m := Nat.find_min' h ⟨hmcap, hzero⟩
      exact (Nat.not_lt_of_ge hmin) (lt_of_le_of_lt hm hq)
    · rintro ⟨hqcap, hzero⟩
      apply Nat.lt_of_not_ge
      intro hfind
      rcases Nat.find_spec h with ⟨_, hne⟩
      exact hne (hzero (Nat.find h) hfind)
  · rw [dif_neg h]
    constructor
    · intro hq
      refine ⟨hq, ?_⟩
      intro m hm
      by_contra hzero
      exact h ⟨m, lt_of_le_of_lt hm hq, hzero⟩
    · rintro ⟨hq, _⟩
      exact hq

/-- At the initial coordinate, continuation of the capped stop is measurable
from the external factor alone. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkCappedStop_continuation_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ) :
    MeasurableSet[MeasurableSpace.comap (Prod.fst :
      MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) →
      MulticlassPalmFutureMarkExternalCarrier i j) inferInstance]
      {z | 0 < stationaryPriorityClassTaggedFutureMarkCappedStop
        meanService i j older cap z} := by
  let U : Set (MulticlassPalmFutureMarkExternalCarrier i j) :=
    {s | 0 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older s = 0}
  have hzero : MeasurableSet
      {s : MulticlassPalmFutureMarkExternalCarrier i j |
        stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older s = 0} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
        meanService i j older (measurableSet_singleton (0 : ℝ)))
  have hU : MeasurableSet U := by
    by_cases hcap : 0 < cap
    · simpa [U, hcap] using hzero
    · simp [U, hcap]
  refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
  ext z
  change (0 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older z.1 = 0) ↔
    0 < stationaryPriorityClassTaggedFutureMarkCappedStop meanService i j older cap z
  rw [lt_stationaryPriorityClassTaggedFutureMarkCappedStop_iff]
  constructor
  · rintro ⟨hcap, hzero⟩
    refine ⟨hcap, ?_⟩
    intro m hm
    have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    rw [stationaryPriorityClassTaggedFutureMarkPrefixObservation_zero]
    exact hzero
  · rintro ⟨hcap, hzero⟩
    refine ⟨hcap, ?_⟩
    have hobs := hzero 0 (Nat.zero_le 0)
    rw [stationaryPriorityClassTaggedFutureMarkPrefixObservation_zero] at hobs
    exact hobs

/-- Evaluate a shorter visible future-mark prefix after restricting an
external-state/IID-prefix observation through coordinate `N`. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (q : Finset.range (N + 1)) :
    MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) → ℝ :=
  fun u => stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older (q.1 + 1)
    (u.1, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
      q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2)) u.2)

/-- Every shorter visible-prefix completion observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (q : Finset.range (N + 1)) :
    Measurable (stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
      meanService i j older N q) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixCompletion
    meanService i j older (q.1 + 1)).comp
  exact measurable_fst.prodMk
    ((AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.measurable_prefixRestriction
      q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))).comp measurable_snd)

/-- Evaluating a visible-prefix completion observation on an actual stream
gives its literal finite-prefix observation. -/
theorem stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion_apply_stateStreamPrefix
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (q : Finset.range (N + 1))
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion meanService i j older N q
      (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
        MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) =
      stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older (q.1 + 1) z := by
  unfold stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
  change stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j older (q.1 + 1)
      (z.1, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
        q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))
          (AppliedModelingLib.Probability.IIDStream.streamPrefix N z.2)) = _
  have hrestriction :
      AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
        q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))
          (AppliedModelingLib.Probability.IIDStream.streamPrefix N z.2) =
        AppliedModelingLib.Probability.IIDStream.streamPrefix q.1 z.2 := by
    simpa only [Function.comp_apply] using congrFun
      (AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction_streamPrefix
        (α := ℝ) q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))) z.2
  rw [hrestriction]
  rfl

/-- At every positive coordinate, continuation of the capped stop is
measurable from the external factor and the preceding IID prefix. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkCappedStop_continuation_succ
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap N : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
        MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N) inferInstance]
      {z | N + 1 < stationaryPriorityClassTaggedFutureMarkCappedStop
        meanService i j older cap z} := by
  let U : Set (MulticlassPalmFutureMarkExternalCarrier i j ×
      (Finset.range (N + 1) → ℝ)) :=
    {u | N + 1 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older u.1 = 0 ∧
      ∀ q : Finset.range (N + 1),
        stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
          meanService i j older N q u = 0}
  have hzero : MeasurableSet
      {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older u.1 = 0} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      ((measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
        meanService i j older).comp measurable_fst (measurableSet_singleton (0 : ℝ)))
  have hvisible : MeasurableSet
      {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        ∀ q : Finset.range (N + 1),
          stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
            meanService i j older N q u = 0} := by
    rw [show {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        ∀ q : Finset.range (N + 1),
          stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
            meanService i j older N q u = 0} =
        ⋂ q : Finset.range (N + 1),
          {u | stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
            meanService i j older N q u = 0} by
      ext u
      simp]
    apply MeasurableSet.iInter
    intro q
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (measurable_stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
        meanService i j older N q (measurableSet_singleton (0 : ℝ)))
  have hU : MeasurableSet U := by
    by_cases hcap : N + 1 < cap
    · have hUeq : U =
          {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
            stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older u.1 = 0} ∩
          {u | ∀ q : Finset.range (N + 1),
            stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion
              meanService i j older N q u = 0} := by
          ext u
          simp [U, hcap]
      rw [hUeq]
      exact hzero.inter hvisible
    · have hUempty : U = ∅ := by
        ext u
        simp [U, hcap]
      rw [hUempty]
      exact MeasurableSet.empty
  refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
  ext z
  change (N + 1 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j older z.1 = 0 ∧
      ∀ q : Finset.range (N + 1),
        stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion meanService i j older N q
          (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
            MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) = 0) ↔
    N + 1 < stationaryPriorityClassTaggedFutureMarkCappedStop meanService i j older cap z
  rw [lt_stationaryPriorityClassTaggedFutureMarkCappedStop_iff]
  constructor
  · rintro ⟨hcap, hzero, hvisible⟩
    refine ⟨hcap, ?_⟩
    intro m hm
    cases m with
    | zero =>
        rw [stationaryPriorityClassTaggedFutureMarkPrefixObservation_zero]
        exact hzero
    | succ m =>
        have hmle : m ≤ N := Nat.succ_le_succ_iff.mp hm
        let q : Finset.range (N + 1) :=
          ⟨m, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hmle)⟩
        have hq := hvisible q
        rw [stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion_apply_stateStreamPrefix
          meanService i j older N q z] at hq
        simpa [q] using hq
  · rintro ⟨hcap, hobs⟩
    refine ⟨hcap, ?_, ?_⟩
    · have hzero := hobs 0 (Nat.zero_le _)
      rw [stationaryPriorityClassTaggedFutureMarkPrefixObservation_zero] at hzero
      exact hzero
    · intro q
      calc
        stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion meanService i j older N q
            (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
              MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) =
            stationaryPriorityClassTaggedFutureMarkPrefixObservation meanService i j older (q.1 + 1) z :=
          stationaryPriorityClassTaggedFutureMarkVisiblePrefixCompletion_apply_stateStreamPrefix
            meanService i j older N q z
        _ = 0 := hobs (q.1 + 1)
          (Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp q.2)))

/-- The capped first-nonzero completion index is predictable with respect to
the isolated IID future-mark stream.  In particular, whether the next mark
is accrued is decided before that mark is revealed. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkCappedPredictableIndex
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ) :
    AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex
      (σ := MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) where
  toFun := stationaryPriorityClassTaggedFutureMarkCappedStop meanService i j older cap
  continuation_zero_measurable :=
    measurableSet_stationaryPriorityClassTaggedFutureMarkCappedStop_continuation_zero
      meanService i j older cap
  continuation_succ_prefix_measurable := fun N =>
    measurableSet_stationaryPriorityClassTaggedFutureMarkCappedStop_continuation_succ
      meanService i j older cap N

/-- The predictable index's underlying function is the concrete capped
first-nonzero completion index. -/
theorem stationaryPriorityClassTaggedFutureMarkCappedPredictableIndex_apply
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkCappedPredictableIndex
      meanService i j older cap z =
      stationaryPriorityClassTaggedFutureMarkCappedStop meanService i j older cap z := rfl

/-- Finite marked-renewal compensation for an isolated passive class: before
the bounded predictable completion index, expected admitted service work is
its mean work requirement times the expected number of continuing marks. -/
theorem integral_truncatedStrictStoppedReward_stationaryPriorityClassTaggedFutureMarkCapped
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ)
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ] (cap : ℕ) :
    ∫ z,
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
        (stationaryPriorityClassTaggedFutureMarkCappedPredictableIndex
          meanService i j older cap)
        (fun work : ℝ => meanService j.1 * work) cap z
        ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))) =
      (∑ r ∈ Finset.range (cap + 1),
        (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))).real
          ((stationaryPriorityClassTaggedFutureMarkCappedPredictableIndex
            meanService i j older cap).continuationEvent r)) * meanService j.1 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hmeasurable : Measurable (fun work : ℝ => meanService j.1 * work) :=
    measurable_const.mul measurable_id
  have hintegrable : Integrable (fun work : ℝ => meanService j.1 * work)
      (ProbabilityTheory.expMeasure (1 : ℝ)) := by
    exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
  have hmean : ∫ work : ℝ, meanService j.1 * work ∂ProbabilityTheory.expMeasure (1 : ℝ) =
      meanService j.1 := by
    rw [MeasureTheory.integral_const_mul,
      AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num)]
    norm_num
  rw [AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.integral_truncatedStrictStoppedReward
    ρ (ProbabilityTheory.expMeasure (1 : ℝ))
    (stationaryPriorityClassTaggedFutureMarkCappedPredictableIndex meanService i j older cap)
    (fun work : ℝ => meanService j.1 * work) hmeasurable hintegrable cap, hmean]

/-- The bounded first diagonal horizon at which the finite tagged-completion
observation is nonzero.  The deterministic cap keeps this a total, genuinely
predictable object before the unbounded summability theorem is available. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℕ := by
  classical
  intro z
  exact if h : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m z ≠ 0
    then Nat.find h else cap

/-- Strict continuation before the diagonal capped stop is equivalent to the
cap not having been reached and all visible diagonal observations vanishing. -/
theorem lt_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap q : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    q < stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap z ↔
      q < cap ∧ ∀ m ≤ q,
        stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m z = 0 := by
  classical
  unfold stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop
  by_cases h : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m z ≠ 0
  · rw [dif_pos h]
    constructor
    · intro hq
      rcases Nat.find_spec h with ⟨hcap, hne⟩
      refine ⟨lt_of_lt_of_le hq (Nat.le_of_lt hcap), ?_⟩
      intro m hm
      by_contra hzero
      have hmcap : m < cap :=
        lt_of_le_of_lt hm (lt_of_lt_of_le hq (Nat.le_of_lt hcap))
      have hmin : Nat.find h ≤ m := Nat.find_min' h ⟨hmcap, hzero⟩
      exact (Nat.not_lt_of_ge hmin) (lt_of_le_of_lt hm hq)
    · rintro ⟨hqcap, hzero⟩
      apply Nat.lt_of_not_ge
      intro hfind
      rcases Nat.find_spec h with ⟨_, hne⟩
      exact hne (hzero (Nat.find h) hfind)
  · rw [dif_neg h]
    constructor
    · intro hq
      refine ⟨hq, ?_⟩
      intro m hm
      by_contra hzero
      exact h ⟨m, lt_of_le_of_lt hm hq, hzero⟩
    · rintro ⟨hq, _⟩
      exact hq

/-- The zero-index diagonal completion observation depends only on the
external factor. -/
theorem stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j 0 z =
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 z.1 := by
  simpa [stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation] using
    (stationaryPriorityClassTaggedFutureMarkPrefixObservation_zero meanService i j 0 z)

/-- A shorter diagonal observation evaluated from a visible IID prefix. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (N : ℕ)
    (q : Finset.range (N + 1)) :
    MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) → ℝ :=
  fun u => stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j
    ((q.1 + 1 : ℕ) : ℝ) (q.1 + 1)
    (u.1, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
      q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2)) u.2)

/-- Every visible diagonal completion observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (N : ℕ)
    (q : Finset.range (N + 1)) :
    Measurable (stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
      meanService i j N q) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixCompletion
    meanService i j ((q.1 + 1 : ℕ) : ℝ) (q.1 + 1)).comp
  exact measurable_fst.prodMk
    ((AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.measurable_prefixRestriction
      q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))).comp measurable_snd)

/-- Restricting an actual stream to its visible prefix recovers the literal
shorter diagonal observation. -/
theorem stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion_apply_stateStreamPrefix
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (N : ℕ)
    (q : Finset.range (N + 1))
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion meanService i j N q
      (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
        MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) =
      stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j (q.1 + 1) z := by
  unfold stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
    stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation
  change stationaryPriorityClassTaggedFutureMarkPrefixCompletion meanService i j
      ((q.1 + 1 : ℕ) : ℝ) (q.1 + 1)
      (z.1, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
        q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))
          (AppliedModelingLib.Probability.IIDStream.streamPrefix N z.2)) = _
  have hrestriction :
      AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
        q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))
          (AppliedModelingLib.Probability.IIDStream.streamPrefix N z.2) =
        AppliedModelingLib.Probability.IIDStream.streamPrefix q.1 z.2 := by
    simpa only [Function.comp_apply] using congrFun
      (AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction_streamPrefix
        (α := ℝ) q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))) z.2
  rw [hrestriction]
  rfl

/-- The initial diagonal continuation event is Borel from the external
factor alone. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_continuation_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    MeasurableSet[MeasurableSpace.comap (Prod.fst :
      MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) →
      MulticlassPalmFutureMarkExternalCarrier i j) inferInstance]
      {z | 0 < stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop
        meanService i j cap z} := by
  let U : Set (MulticlassPalmFutureMarkExternalCarrier i j) :=
    {s | 0 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 s = 0}
  have hzero : MeasurableSet
      {s : MulticlassPalmFutureMarkExternalCarrier i j |
        stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 s = 0} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
        meanService i j 0 (measurableSet_singleton (0 : ℝ)))
  have hU : MeasurableSet U := by
    by_cases hcap : 0 < cap
    · simpa [U, hcap] using hzero
    · simp [U, hcap]
  refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
  ext z
  change (0 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 z.1 = 0) ↔
    0 < stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap z
  rw [lt_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_iff]
  constructor
  · rintro ⟨hcap, hzero⟩
    refine ⟨hcap, ?_⟩
    intro m hm
    have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    rw [stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_zero]
    exact hzero
  · rintro ⟨hcap, hzero⟩
    refine ⟨hcap, ?_⟩
    have hobs := hzero 0 (Nat.zero_le 0)
    rw [stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_zero] at hobs
    exact hobs

/-- At every positive coordinate, diagonal continuation is measurable from
the external factor and precisely the preceding IID mark prefix. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_continuation_succ
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap N : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
        MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N) inferInstance]
      {z | N + 1 < stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop
        meanService i j cap z} := by
  let U : Set (MulticlassPalmFutureMarkExternalCarrier i j ×
      (Finset.range (N + 1) → ℝ)) :=
    {u | N + 1 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 u.1 = 0 ∧
      ∀ q : Finset.range (N + 1),
        stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
          meanService i j N q u = 0}
  have hzero : MeasurableSet
      {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 u.1 = 0} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      ((measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion
        meanService i j 0).comp measurable_fst (measurableSet_singleton (0 : ℝ)))
  have hvisible : MeasurableSet
      {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        ∀ q : Finset.range (N + 1),
          stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
            meanService i j N q u = 0} := by
    rw [show {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        ∀ q : Finset.range (N + 1),
          stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
            meanService i j N q u = 0} =
        ⋂ q : Finset.range (N + 1),
          {u | stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
            meanService i j N q u = 0} by
      ext u
      simp]
    apply MeasurableSet.iInter
    intro q
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (measurable_stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
        meanService i j N q (measurableSet_singleton (0 : ℝ)))
  have hU : MeasurableSet U := by
    by_cases hcap : N + 1 < cap
    · have hUeq : U =
          {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
            stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 u.1 = 0} ∩
          {u | ∀ q : Finset.range (N + 1),
            stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion
              meanService i j N q u = 0} := by
          ext u
          simp [U, hcap]
      rw [hUeq]
      exact hzero.inter hvisible
    · have hUempty : U = ∅ := by
        ext u
        simp [U, hcap]
      rw [hUempty]
      exact MeasurableSet.empty
  refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
  ext z
  change (N + 1 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixCompletion meanService i j 0 z.1 = 0 ∧
      ∀ q : Finset.range (N + 1),
        stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion meanService i j N q
          (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
            MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) = 0) ↔
    N + 1 < stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap z
  rw [lt_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_iff]
  constructor
  · rintro ⟨hcap, hzero, hvisible⟩
    refine ⟨hcap, ?_⟩
    intro m hm
    cases m with
    | zero =>
        rw [stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_zero]
        exact hzero
    | succ m =>
        have hmle : m ≤ N := Nat.succ_le_succ_iff.mp hm
        let q : Finset.range (N + 1) :=
          ⟨m, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hmle)⟩
        have hq := hvisible q
        rw [stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion_apply_stateStreamPrefix
          meanService i j N q z] at hq
        simpa [q] using hq
  · rintro ⟨hcap, hobs⟩
    refine ⟨hcap, ?_, ?_⟩
    · have hzero := hobs 0 (Nat.zero_le _)
      rw [stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_zero] at hzero
      exact hzero
    · intro q
      calc
        stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion meanService i j N q
            (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
              MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) =
            stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j (q.1 + 1) z :=
          stationaryPriorityClassTaggedFutureMarkDiagonalVisiblePrefixCompletion_apply_stateStreamPrefix
            meanService i j N q z
        _ = 0 := hobs (q.1 + 1)
          (Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp q.2)))

/-- The diagonal capped first-completion index is predictable with respect to
the isolated IID future-mark stream. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex
      (σ := MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) where
  toFun := stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap
  continuation_zero_measurable :=
    measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_continuation_zero
      meanService i j cap
  continuation_succ_prefix_measurable := fun N =>
    measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_continuation_succ
      meanService i j cap N

/-- The predictable diagonal index has the intended concrete stopping
function. -/
theorem stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex_apply
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
      meanService i j cap z =
    stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap z := rfl

/-- The unused future service-mark tail after a capped diagonal completion
stop has its original IID exponential law.  This is a restart statement for
the literal factored queue carrier; it does not by itself provide the
summability estimate needed for the uncapped compensation formula. -/
theorem stationaryPriorityClassTaggedFutureMarkDiagonalCappedPostTail_hasLaw
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ] (cap : ℕ) :
    ProbabilityTheory.HasLaw
      (AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.postTail
        ((stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
          meanService i j cap).toStatePrefixStoppingIndex))
      (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure (1 : ℝ)))
      (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure (1 : ℝ))) ) := by
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  simpa [μ] using
    (AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.postTail_hasLaw
      ρ μ
      ((stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
        meanService i j cap).toStatePrefixStoppingIndex))

/-- Finite marked-renewal compensation for the diagonal selected-completion
index.  This is the valid bounded precursor to the remaining unbounded
summability argument. -/
theorem integral_truncatedStrictStoppedReward_stationaryPriorityClassTaggedFutureMarkDiagonalCapped
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ] (cap : ℕ) :
    ∫ z,
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
        (stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
          meanService i j cap)
        (fun work : ℝ => meanService j.1 * work) cap z
        ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))) =
      (∑ r ∈ Finset.range (cap + 1),
        (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))).real
          ((stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
            meanService i j cap).continuationEvent r)) * meanService j.1 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hmeasurable : Measurable (fun work : ℝ => meanService j.1 * work) :=
    measurable_const.mul measurable_id
  have hintegrable : Integrable (fun work : ℝ => meanService j.1 * work)
      (ProbabilityTheory.expMeasure (1 : ℝ)) := by
    exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
  have hmean : ∫ work : ℝ, meanService j.1 * work ∂ProbabilityTheory.expMeasure (1 : ℝ) =
      meanService j.1 := by
    rw [MeasureTheory.integral_const_mul,
      AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num)]
    norm_num
  rw [AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.integral_truncatedStrictStoppedReward
    ρ (ProbabilityTheory.expMeasure (1 : ℝ))
    (stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex meanService i j cap)
    (fun work : ℝ => meanService j.1 * work) hmeasurable hintegrable cap, hmean]

/-- Under strict load, an almost-surely finite diagonal completion is found
strictly before every sufficiently large deterministic cap.  This is a
termination statement only; it deliberately makes no claim about the rate at
which the continuation probabilities decay. -/
theorem ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_lt_cap
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∀ᶠ cap : ℕ in Filter.atTop,
        stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap x < cap := by
  filter_upwards [ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_ne_zero
    arrivalRate meanService harrivalRate hmeanService hstable i j] with x hx
  rcases Filter.eventually_atTop.1 hx with ⟨first, hfirst⟩
  apply Filter.eventually_atTop.2
  refine ⟨first + 1, ?_⟩
  intro cap hcap
  have hfound : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m x ≠ 0 := by
    refine ⟨first, ?_, hfirst first le_rfl⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self first) hcap
  rw [show stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop meanService i j cap x =
      Nat.find hfound by
    unfold stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop
    exact dif_pos hfound]
  exact (Nat.find_spec hfound).1

/-- The predictable event that the diagonal tagged-completion observation has
not yet appeared through coordinate `n`. -/
def stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (index : ℕ) :
    Set (MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :=
  {z | ∀ m ≤ index,
    stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m z = 0}

/-- The diagonal continuation event is exactly the corresponding event of a
cap chosen one coordinate beyond it. -/
theorem stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_eq_capped
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (index : ℕ) :
    stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent meanService i j index =
      (stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
        meanService i j (index + 1)).continuationEvent index := by
  ext z
  change (∀ m ≤ index,
    stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m z = 0) ↔
    index < stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop
      meanService i j (index + 1) z
  rw [lt_stationaryPriorityClassTaggedFutureMarkDiagonalCappedStop_iff]
  simp

/-- Every diagonal continuation event is Borel measurable from the prefix
available before the corresponding IID service mark. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (index : ℕ) :
    MeasurableSet
      (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent meanService i j index) := by
  rw [stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_eq_capped]
  exact (stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
    meanService i j (index + 1)).measurableSet_continuationEvent index

/-- Total isolated-class service work admitted while the diagonal tagged
completion remains pending. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ := by
  classical
  exact fun z => ∑' index,
    if z ∈ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index then meanService j.1 *
        AppliedModelingLib.Probability.IIDStream.coordinate index z.2 else 0

/-- The extended nonnegative version of the diagonal admitted-work
observable.  Tonelli applies directly to this observable, so its expectation
is meaningful before a finite-tail estimate has been established. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ENNReal := by
  classical
  exact fun z => ∑' index,
    if z ∈ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index then ENNReal.ofReal (meanService j.1 *
        AppliedModelingLib.Probability.IIDStream.coordinate index z.2) else 0

/-- Extended nonnegative marked-renewal compensation for the diagonal
selected-completion observation.  No summability premise is needed here:
Tonelli records both sides in `ℝ≥0∞`.  Establishing that the displayed tail
sum is finite still requires a queue-specific truncation or tail estimate. -/
theorem lintegral_stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ] (hmean : 0 < meanService j.1) :
    ∫⁻ z,
      stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward meanService i j z
      ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure (1 : ℝ)))) =
      (∑' index,
        (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ))))
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index)) * ENNReal.ofReal (meanService j.1) := by
  classical
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let M : Measure (MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :=
    ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ)
  let reward : ℝ → ENNReal := fun work => ENNReal.ofReal (meanService j.1 * work)
  let F : ℕ → MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ENNReal :=
    fun index z => if z ∈ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index then reward
        (AppliedModelingLib.Probability.IIDStream.coordinate index z.2) else 0
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure μ) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hreward : Measurable reward :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)
  have hF_measurable : ∀ index, Measurable (F index) := by
    intro index
    have hcoordinate : Measurable
        (fun z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) =>
          reward (AppliedModelingLib.Probability.IIDStream.coordinate index z.2)) :=
      hreward.comp ((AppliedModelingLib.Probability.IIDStream.measurable_coordinate (α := ℝ) index).comp
        measurable_snd)
    have hindicator := hcoordinate.indicator
      (measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index)
    have heq : F index =
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent meanService i j index).indicator
          (fun z => reward (AppliedModelingLib.Probability.IIDStream.coordinate index z.2)) := by
      funext z
      simp [F, Set.indicator]
    rw [heq]
    exact hindicator
  have hterm (index : ℕ) :
      ∫⁻ z, F index z ∂M =
        M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) * ∫⁻ work, reward work ∂μ := by
    let τ := stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
      meanService i j (index + 1)
    have hτ : stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index = τ.continuationEvent index := by
      exact stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_eq_capped
        meanService i j index
    have hcomp := AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.lintegral_continuationEvent_indicator_mul_coordinate
      ρ μ τ index reward hreward
    simpa [F, M, hτ,
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.continuationEvent] using hcomp
  have hmeanReward : ∫⁻ work, reward work ∂μ = ENNReal.ofReal (meanService j.1) := by
    have hintegrable : Integrable (fun work : ℝ => meanService j.1 * work) μ := by
      dsimp [μ]
      exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
    let expModel : AppliedModelingLib.Probability.Exponential.Model :=
      ⟨1, by norm_num⟩
    have hnonnegative : 0 ≤ᵐ[μ] fun work : ℝ => meanService j.1 * work := by
      change 0 ≤ᵐ[expModel.measure] fun work : ℝ => meanService j.1 * work
      filter_upwards [expModel.ae_nonnegative] with work hwork
      exact mul_nonneg hmean.le hwork
    calc
      ∫⁻ work, reward work ∂μ =
          ENNReal.ofReal (∫ work, meanService j.1 * work ∂μ) := by
            dsimp [reward]
            exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              hintegrable hnonnegative).symm
      _ = ENNReal.ofReal (meanService j.1) := by
            rw [MeasureTheory.integral_const_mul,
              AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num)]
            norm_num
  calc
    ∫⁻ z,
        stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward meanService i j z
        ∂M = ∫⁻ z, ∑' index, F index z ∂M := by
          rfl
    _ = ∑' index, ∫⁻ z, F index z ∂M := by
      exact MeasureTheory.lintegral_tsum fun index => (hF_measurable index).aemeasurable
    _ = ∑' index,
        M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) * ∫⁻ work, reward work ∂μ := by
      apply tsum_congr
      exact hterm
    _ = (∑' index,
        M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) * ∫⁻ work, reward work ∂μ := by
      rw [ENNReal.tsum_mul_right]
    _ = (∑' index,
        M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) * ENNReal.ofReal (meanService j.1) := by
      rw [hmeanReward]

/-- The unbounded diagonal marked-work compensation identity, conditional on
the explicitly stated continuation-probability summability condition.  The
condition is the remaining queue-specific tail theorem, not a consequence of
almost-sure finite completion alone. -/
theorem integral_stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ]
    (hsummable : Summable fun index =>
      (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure (1 : ℝ)))).real
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) :
    ∫ z, stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward meanService i j z
      ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure (1 : ℝ)))) =
      (∑' index,
        (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))).real
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index)) * meanService j.1 := by
  classical
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let M : Measure (MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :=
    ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ)
  let reward : ℝ → ℝ := fun work => meanService j.1 * work
  let F : ℕ → MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun index z => if z ∈ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index then reward
        (AppliedModelingLib.Probability.IIDStream.coordinate index z.2) else 0
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (AppliedModelingLib.Probability.IIDStream.measure μ) := by
    dsimp [AppliedModelingLib.Probability.IIDStream.measure]
    infer_instance
  have hmeasurable : Measurable reward := measurable_const.mul measurable_id
  have hintegrable : Integrable reward μ := by
    dsimp [reward, μ]
    exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
  have hF_integrable : ∀ index, Integrable (F index) M := by
    intro index
    have hcoordinate : Integrable (fun z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) =>
        reward (AppliedModelingLib.Probability.IIDStream.coordinate index z.2)) M := by
      simpa [M, Function.comp_def] using
        ((AppliedModelingLib.Probability.IIDStream.coordinate_measurePreserving μ index).comp
          (measurePreserving_snd : MeasurePreserving Prod.snd
            (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ))
            (AppliedModelingLib.Probability.IIDStream.measure μ))).integrable_comp_of_integrable hintegrable
    have hindicator := hcoordinate.indicator
      (measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index)
    have heq : F index =
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent meanService i j index).indicator
          (fun z => reward (AppliedModelingLib.Probability.IIDStream.coordinate index z.2)) := by
      funext z
      simp [F, Set.indicator]
    rw [heq]
    exact hindicator
  have hintegral (index : ℕ) :
      ∫ z, F index z ∂M =
        M.real (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) * ∫ work, reward work ∂μ := by
    let τ := stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
      meanService i j (index + 1)
    have hτ : stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index = τ.continuationEvent index := by
      exact stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_eq_capped
        meanService i j index
    have hcomp := AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.integral_continuationEvent_indicator_mul_coordinate
        ρ μ τ index reward hmeasurable
    simpa [F, M, hτ,
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.continuationEvent] using hcomp
  have hnormIntegral : ∀ index,
      ∫ z, ‖F index z‖ ∂M =
        M.real (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) * ∫ work, ‖reward work‖ ∂μ := by
    intro index
    let rewardNorm : ℝ → ℝ := fun work => ‖reward work‖
    let τ := stationaryPriorityClassTaggedFutureMarkDiagonalCappedPredictableIndex
      meanService i j (index + 1)
    have hτ : stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index = τ.continuationEvent index := by
      exact stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_eq_capped
        meanService i j index
    have hcomp := AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.integral_continuationEvent_indicator_mul_coordinate
        ρ μ τ index rewardNorm hmeasurable.norm
    simpa [F, M, rewardNorm, hτ, apply_ite,
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.continuationEvent] using hcomp
  have hsumNorm : Summable fun index => ∫ z, ‖F index z‖ ∂M := by
    have hsum : Summable fun index =>
        M.real (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) := by
      simpa [M, μ] using hsummable
    exact (hsum.mul_right (∫ work, ‖reward work‖ ∂μ)).congr fun index =>
      (hnormIntegral index).symm
  calc
    ∫ z, stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward meanService i j z ∂M =
        ∫ z, ∑' index, F index z ∂M := by
          rfl
    _ = ∑' index, ∫ z, F index z ∂M := by
      exact (MeasureTheory.integral_tsum_of_summable_integral_norm
        hF_integrable hsumNorm).symm
    _ = ∑' index,
        M.real (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) * ∫ work, reward work ∂μ := by
      apply tsum_congr
      intro index
      exact hintegral index
    _ = (∑' index,
        M.real (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) * ∫ work, reward work ∂μ := by
      rw [tsum_mul_right]
    _ = (∑' index,
        M.real (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) * meanService j.1 := by
      have hmean : ∫ work, reward work ∂μ = meanService j.1 := by
        dsimp [reward, μ]
        rw [MeasureTheory.integral_const_mul,
          AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num)]
        norm_num
      rw [hmean]

/-- The diagonal marked-work compensation identity on the actual selected-Palm
external-factor law.  Its summability premise is intentionally explicit: it
is the remaining stationary-priority tail estimate needed to use this finite
compensation result for the concrete queue. -/
theorem integral_stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward_of_summable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i})
    (hsummable : Summable fun index =>
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).real
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) :
    ∫ z, stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward meanService i j z
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      (∑' index,
        ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).real
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index)) * meanService j.1 := by
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  simpa [AppliedModelingLib.Probability.IIDStream.measure,
    Probability.PoissonProcess.exponentialInterarrivalMeasure] using
    (integral_stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedReward
      meanService i j (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) hsummable)

/-- The extended count of isolated-class arrivals at which the diagonal tagged
completion is still pending.  It is allowed to be infinite on exceptional
paths; finite expectation is precisely the condition that upgrades the
extended nonnegative compensation identity to a real-valued one. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ENNReal := by
  classical
  exact fun z => ∑' index,
    (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index).indicator (fun _ => (1 : ENNReal)) z

/-- Tonelli's identity for the diagonal pending-arrival count.  The right
side is the extended tail sum; its finiteness is needed only to pass to the
finite real-valued compensation identity. -/
theorem lintegral_stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫⁻ z, stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      ∑' index,
        ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index) := by
  classical
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  change ∫⁻ z, ∑' index,
      (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index).indicator (fun _ => (1 : ENNReal)) z ∂M = _
  calc
    ∫⁻ z, ∑' index,
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index).indicator (fun _ => (1 : ENNReal)) z ∂M =
        ∑' index, ∫⁻ z,
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index).indicator (fun _ => (1 : ENNReal)) z ∂M :=
      MeasureTheory.lintegral_tsum fun index =>
        (measurable_const.indicator
          (measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index)).aemeasurable
    _ = ∑' index,
        M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) := by
      apply tsum_congr
      intro index
      exact MeasureTheory.lintegral_indicator_one
        (measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)

/-- On the concrete selected-Palm factor, the extended expected isolated
class work accrued while the tag remains pending is the class mean times the
extended expected number of pending isolated-class arrivals.  This is the
nonnegative compensation identity used before finiteness has been derived. -/
theorem lintegral_stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward_eq_mean_mul_pendingCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫⁻ z,
      stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward meanService i j z
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      ENNReal.ofReal (meanService j.1) *
        ∫⁻ z, stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z
          ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let ρ := multiclassPalmFutureMarkExternalMeasure arrivalRate i j
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let M := ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ)
  letI : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  have hwork := lintegral_stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward
    meanService i j ρ (hmeanService j.1)
  have hcount := lintegral_stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount
    arrivalRate meanService harrivalRate i j
  rw [show (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) =
      AppliedModelingLib.Probability.IIDStream.measure μ by
        rfl]
  change ∫⁻ z,
      stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward meanService i j z ∂M =
      ENNReal.ofReal (meanService j.1) * ∫⁻ z,
        stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z ∂M
  rw [show M = ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ) by rfl]
  rw [show ∫⁻ z,
      stationaryPriorityClassTaggedFutureMarkDiagonalStrictStoppedENNReward meanService i j z ∂M =
      (∑' index, M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index)) * ENNReal.ofReal (meanService j.1) by
      simpa [M, μ] using hwork]
  rw [show ∫⁻ z,
      stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z ∂M =
      ∑' index, M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index) by
      simpa [M, μ] using hcount]
  exact mul_comm _ _

/-- For the concrete selected-Palm factor law, continuation-probability
summability is equivalent to finite expected diagonal pending-arrival count.
This identifies the exact finiteness condition needed to pass from extended
nonnegative accounting to the ordinary real-valued balance. -/
theorem summable_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_iff
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    (Summable fun index =>
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).real
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) ↔
      ∫⁻ z, stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) ≠ ⊤ := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hTonelli : ∫⁻ z,
      stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z ∂M =
      ∑' index, M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index) := by
    simpa [M] using
      (lintegral_stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount
        arrivalRate meanService harrivalRate i j)
  constructor
  · intro hsummable
    rw [hTonelli]
    have hterm : ∀ index,
        ENNReal.ofReal (M.real
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index)) =
        M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) := by
      intro index
      exact ENNReal.ofReal_toReal
        (measure_ne_top M
          (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
            meanService i j index))
    rw [← tsum_congr hterm]
    exact hsummable.tsum_ofReal_ne_top
  · intro hfinite
    rw [hTonelli] at hfinite
    exact ENNReal.summable_toReal hfinite

/-- A geometric continuation bound supplies the summability needed for the
unbounded diagonal marked-work compensation formula.  The bound itself is the
queue-specific busy-period estimate; this theorem only performs the analytic
summation step. -/
theorem summable_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_of_geometric_bound
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (i : Fin n) (j : {k : Fin n // k ≠ i})
    (r : ℝ) (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hbound : ∀ index,
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).real
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) ≤ r ^ index) :
    Summable fun index =>
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).real
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index) := by
  apply Summable.of_nonneg_of_le
  · intro index
    exact MeasureTheory.measureReal_nonneg
  · exact hbound
  · exact summable_geometric_of_lt_one hr_nonneg hr_lt_one

/-- Strict load makes the diagonal pending-arrival count finite on almost every
path.  This is a pathwise termination statement only: its expectation can
still be infinite, so it does not imply the summability condition above. -/
theorem ae_stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ z ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      stationaryPriorityClassTaggedFutureMarkDiagonalPendingCount meanService i j z ≠ ⊤ := by
  classical
  filter_upwards [
    ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_ne_zero
      arrivalRate meanService harrivalRate hmeanService hstable i j] with z hz
  rcases (Filter.eventually_atTop.1 hz) with ⟨N, hN⟩
  let f : ℕ → ENNReal := fun index =>
    (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index).indicator (fun _ => (1 : ENNReal)) z
  have hfzero : ∀ index ∉ Finset.range N, f index = 0 := by
    intro index hnotrange
    have hNindex : N ≤ index := Nat.le_of_not_gt (by simpa using hnotrange)
    have hnotmem : z ∉ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index := by
      intro hmem
      change ∀ m ≤ index,
        stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m z = 0
        at hmem
      exact (hN N le_rfl) (hmem N hNindex)
    simp [f, Set.indicator_of_notMem hnotmem]
  change ∑' index, f index ≠ ⊤
  rw [tsum_eq_sum hfzero]
  apply ENNReal.sum_ne_top.2
  intro index _
  by_cases hmem : z ∈ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index
  · simp [f, hmem]
  · simp [f, hmem]

/-- Strict load makes the diagonal pending-completion probabilities converge
to zero.  This is the exact consequence of almost-sure eventual completion;
it is intentionally not stated as summability. -/
theorem tendsto_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent_real_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    Filter.Tendsto (fun index =>
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))).real
        (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
          meanService i j index)) Filter.atTop (nhds 0) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hlimit : ∀ᵐ x ∂M, ∀ᶠ index : ℕ in Filter.atTop,
      x ∈ stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index ↔ x ∈ (∅ : Set (MulticlassPalmFutureMarkExternalCarrier i j ×
          (ℕ → ℝ))) := by
    filter_upwards [
      ae_eventually_stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation_ne_zero
        arrivalRate meanService harrivalRate hmeanService hstable i j] with x hx
    filter_upwards [hx] with index hindex
    constructor
    · intro hcontinuation
      change ∀ m ≤ index,
        stationaryPriorityClassTaggedFutureMarkDiagonalPrefixObservation meanService i j m x = 0
          at hcontinuation
      exact (hindex (hcontinuation index le_rfl)).elim
    · intro hempty
      exact False.elim (by simpa using hempty)
  have hmeasure : Filter.Tendsto (fun index =>
      M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index)) Filter.atTop (nhds (M ∅)) := by
    exact MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (L := Filter.atTop) (A := ∅)
      MeasurableSet.empty
      (measurableSet_stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j) hlimit
  change Filter.Tendsto (fun index =>
    (M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
      meanService i j index)).toReal) Filter.atTop (nhds 0)
  have hmeasurezero : Filter.Tendsto (fun index =>
      M (stationaryPriorityClassTaggedFutureMarkDiagonalContinuationEvent
        meanService i j index)) Filter.atTop (nhds 0) := by
    simpa using hmeasure
  simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasurezero

end

end AppliedModelingLib.Queueing
